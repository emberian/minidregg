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

**The program record (E3).** `Params` are the evaluator's own entry data, carried as the
record's `params` bytes and decoded only here (`decodeParams`, canonical by
`decodeParams_canonical`; Nock's are the arm, `Kernel.NockEntry.encodeParams`). The sample is
the generic record `Kernel.NockProgramCell.Sample` (`sampleRecord`: context, targets,
`(key, value)` per ABI slot) encoded under the ABI's layout (`encodeSample`, injective under
one layout: `encodeSample_injective`); `Machine.sampleOf` is the composite, and
`Evaluator.sampleOf_injective` is EVAL §1.1's corollary. A record is admitted at birth by
`admitRecord`: its evaluator resolves against the registry (`resolve`: `unknownEvaluator`,
`evaluatorDisabled`) and the record passes that evaluator's `admit` (code, ABI, names
without NUL, params).

**Doors (E4).** `door : Option EvalDoor`: boot+poke, peek, load, the state's encoding as a
field value, and the event a claim carries — EVAL §4. Nock's is N11's (`nockDoor`, from
`Kernel.NockEntry`); the referee is `Kernel.Door`, generic.
-/
import Kernel.NockEntry
import Theory.TypedAuthorization
import Compiler.Sp800185Cshake256

namespace Minidregg.Compiler

open Minidregg.Theory
open Minidregg.Theory.Eval
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler.NockProgramCodec (Abi SampleSlot OutputSlot Program EffectRefusal
  NamesNulFree AbiShape abiVersion)
open Minidregg.Kernel.NockProgramCell (Context Sample sampleRecord)

set_option autoImplicit false

/-- EVAL §4's door, evaluator-generic: a program whose state lives in a cell (N11). Data
only; the facts are `Evaluator`'s. The ABI's door record (`NockProgramCodec.Door`: the peek
arm, the state and event fields) says WHERE the state lives; this says how the evaluator
boots, pokes and peeks it. -/
structure EvalDoor (Params Code Input Output Term : Type) where
  /-- What a poke carries besides the state and the event number (Nock: `(wire, cause)`). -/
  Event : Type
  /-- The state as the field value it is stored as (Nock: `jamAtom`). -/
  encodeState : Output → Nat
  /-- A stored field value as a state, refused unless it is a state's encoding (Nock: `ofJamAtom`). -/
  decodeState : Nat → Option Output
  /-- The sample a poke's claim names: the stored state (`none`: never poked), the event
  number, the event (Nock: `[ustate job]`). -/
  pokeInput : Option Output → Nat → Event → Input
  /-- The event a claimed sample's bytes carry, when they are a poke's. -/
  eventOf : List UInt8 → Option Event
  /-- **boot + poke**: the term a poke runs (Nock: boot the trap with `[9 2 0 1]`, re-install
  the stored state at axis 6, slam the params' arm on the job). -/
  poke : Params → Code → Option Output → Nat → Event → Term
  /-- The poke's product as `(effects, next state)`; `none` when it breaks the door's shape
  (Nock: `core' = #[6 state' door]`). -/
  product : Output → Option (Output × Output)
  /-- The output a poke's claim names (Nock: `[effects state']`). -/
  claimOutput : Output → Output → Output
  /-- The effects, as writes against the ABI's outputs. -/
  effects : List OutputSlot → Output → Except EffectRefusal (List FieldWrite)
  /-- **peek**: the term a read runs on a path over the stored state, at the ABI's peek arm. -/
  peek : Code → Option Output → Nat → Input → Term
  /-- **load**: the term that reads the door's state now (the stored one, or the booted trap's). -/
  load : Code → Option Output → Term

/-- What an evaluator computes with: the machine, its byte forms, and the kernel's
run (params, entry, oracle, writes, sample, door). No facts; those are `Evaluator`'s. -/
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
  -- The program record's params (E3)
  /-- The evaluator's own entry data (Nock: the arm). -/
  Params : Type
  encodeParams : Params → List UInt8
  /-- The record's `params` bytes, decoded (fail-closed). -/
  decodeParams : List UInt8 → Option Params
  /-- The evaluator's birth check of its params (Nock: arm 0 refuses `armZero`). -/
  checkParams : Params → Option NockProgramCodec.Refusal
  -- The kernel's run
  /-- The term the kernel runs: the program's code under its params, over its
  libraries' code (ABI order), on the sample (Nock: N16's `subjectFormula params.arm`). -/
  entry : Params → Code → List Code → Input → Term
  /-- One fueled evaluation in a single pass, the count kept on every outcome. -/
  oracle : Nat → Term → Ran Output
  /-- The writes a product names against the ABI's outputs (Nock: `decodeWrites`). -/
  writesOf : Abi → Output → Option (List FieldWrite)
  -- The sample (E3): the generic record, encoded under the ABI's layout
  /-- The record as the machine sees it, under a layout (the ABI's sample slots): the
  layout names every key the encoding writes. -/
  encodeSample : List SampleSlot → Sample → Option Input
  /-- The first slot whose value lies above its declared maximum (NC-2). -/
  overMax : (Nat → String → Option Int) → List SampleSlot → Option SampleSlot
  /-- Which named slot a stale claim's sample missed (K-RUN-PIN), when it can say. -/
  staleField : Abi → Input → List UInt8 → Option String
  -- Doors (E4)
  /-- The evaluator's doors, if it has them (EVAL §4). -/
  door : Option (EvalDoor Params Code Input Output Term)

/-- **The kernel's sample** on any evaluator: the generic record (`sampleRecord`, which
reads the ABI and the projected slots), encoded under the ABI's layout. -/
def Machine.sampleOf (M : Machine) (abi : Abi) (ctx : Context) (targets : List Nat)
    (read : Nat → String → Option Int) : Option M.Input :=
  (sampleRecord abi ctx targets read).bind (M.encodeSample abi.sample)

/-- **`sampleOf_pinned_of_fields`** (K-RUN-PIN), on any evaluator: a pinned program's sample is
a function of the named slots and the targets alone. Generic: the record's. -/
theorem Machine.sampleOf_pinned_of_fields (M : Machine) {abi : Abi} (pinned : abi.context = .pinned)
    (ctx ctx' : Context) (targets : List Nat) {read read' : Nat → String → Option Int}
    (agree : ∀ slot ∈ abi.sample, read slot.target slot.slot = read' slot.target slot.slot) :
    M.sampleOf abi ctx targets read = M.sampleOf abi ctx' targets read' := by
  unfold Machine.sampleOf
  rw [Kernel.NockProgramCell.sampleRecord_pinned_of_fields pinned ctx ctx' targets agree]

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
  -- The params (E3)
  decodeParams_encode : ∀ params, decodeParams (encodeParams params) = some params
  /-- **`decodeParams_canonical`**: accepted params bytes are their value's encoding, so the
  params `programId` covers are a function of the params the kernel runs with. -/
  decodeParams_canonical : ∀ {bytes : List UInt8} {params : Params},
    decodeParams bytes = some params → encodeParams params = bytes
  -- The sample
  /-- **`encodeSample_injective`** (E3): under one layout, the input determines the record. -/
  encodeSample_injective : ∀ {layout : List SampleSlot} {s s' : Sample} {i : Input},
    encodeSample layout s = some i → encodeSample layout s' = some i → s = s'
  sampleOf_overMax : ∀ {abi : Abi} {ctx : Context} {targets : List Nat}
    {read : Nat → String → Option Int} {slot : SampleSlot},
    overMax read abi.sample = some slot →
      (sampleRecord abi ctx targets read).bind (encodeSample abi.sample) = none
  /-- `overMax` reads only the named slots. -/
  overMax_congr : ∀ {read read' : Nat → String → Option Int} {slots : List SampleSlot},
    (∀ s ∈ slots, read s.target s.slot = read' s.target s.slot) →
      overMax read slots = overMax read' slots
  /-- Moving exactly one named slot of a pinned program moves its sample, and
  `staleField` names that slot on the earlier sample's bytes. -/
  staleField_names : ∀ {abi : Abi} {ctx ctx' : Context} {targets : List Nat}
    {read read' : Nat → String → Option Int} {s s' : Input} {slot : SampleSlot},
    abi.context = .pinned → (sampleRecord abi ctx targets read).bind (encodeSample abi.sample) = some s →
    (sampleRecord abi ctx' targets read').bind (encodeSample abi.sample) = some s' →
    slot ∈ abi.sample → read slot.target slot.slot ≠ read' slot.target slot.slot →
    (∀ x ∈ abi.sample, x ≠ slot → read x.target x.slot = read' x.target x.slot) →
    s ≠ s' ∧ staleField abi s' (encodeInput s) = some slot.key
  -- Doors (E4)
  /-- **The door's state codec round-trips** (EVAL §4's `decode_encode`): a stored state always
  reads back, so `stateMalformed` refuses only bytes no poke wrote. -/
  door_decode_encode : ∀ d ∈ door, ∀ state, d.decodeState (d.encodeState state) = some state
  /-- A poke's sample carries its event, recoverable from the bytes. -/
  door_eventOf : ∀ d ∈ door, ∀ (stored : Option Output) (event : Nat) (ev : d.Event),
    d.eventOf (encodeInput (d.pokeInput stored event ev)) = some ev
  /-- A poke's sample determines the state, the event number and the event it was made on. -/
  door_pokeInput_injective : ∀ d ∈ door, ∀ {stored stored' : Option Output} {event event' : Nat}
    {ev ev' : d.Event}, d.pokeInput stored event ev = d.pokeInput stored' event' ev' →
      stored = stored' ∧ event = event' ∧ ev = ev'

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

/-- N11's door, as EVAL §4's three fields (and the state codec): boot `[9 2 0 1]`, poke by
slamming the params' arm on `[ustate job]`, peek by slamming the ABI's peek arm on a path;
the state stored as its jam atom. Every piece is `Kernel.NockEntry`'s. -/
def nockDoor : EvalDoor Kernel.NockEntry.Params Noun Noun Noun (Noun × Noun) where
  Event := Noun × Noun
  encodeState := Kernel.NockProgramCell.jamAtom
  decodeState := Kernel.NockProgramCell.ofJamAtom
  pokeInput stored event ev :=
    .cell (Kernel.NockEntry.ustateNoun stored) (Kernel.NockEntry.job event ev.1 ev.2)
  eventOf bytes := (Noun.cue bytes).bind Kernel.NockEntry.eventOf
  poke params trap stored event ev :=
    (Kernel.NockEntry.subjectOf trap (Kernel.NockEntry.ustateNoun stored)
      (Kernel.NockEntry.job event ev.1 ev.2), Kernel.NockEntry.pokeFormula params.arm)
  product out := (Kernel.NockEntry.pokeProduct out).map fun p => (p.2.1, p.2.2)
  claimOutput effects state := .cell effects state
  effects := Kernel.NockEntry.decodeEffects
  peek trap stored axis path :=
    (Kernel.NockEntry.subjectOf trap (Kernel.NockEntry.ustateNoun stored) path,
      Kernel.NockEntry.peekFormula axis)
  load trap stored :=
    (Kernel.NockEntry.subjectOf trap (Kernel.NockEntry.ustateNoun stored) (.atom 0),
      Kernel.NockEntry.stateFormula)

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
  Params := Kernel.NockEntry.Params
  encodeParams := Kernel.NockEntry.encodeParams
  decodeParams := Kernel.NockEntry.decodeParams
  checkParams := Kernel.NockEntry.checkParams
  entry params code libs sample := Kernel.NockEntry.subjectFormula params.arm code libs sample
  oracle fuel t := Kernel.NockEntry.oracle fuel t.1 t.2
  writesOf := Kernel.NockEntry.decodeWrites
  encodeSample := Kernel.NockProgramCell.encodeSample
  overMax := Kernel.NockProgramCell.overMax
  staleField := Kernel.NockEntry.staleField
  door := some nockDoor

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
  decodeParams_encode := Kernel.NockEntry.decodeParams_encode
  decodeParams_canonical h := Kernel.NockEntry.decodeParams_canonical h
  encodeSample_injective h h' := Kernel.NockProgramCell.encodeSample_injective h h'
  sampleOf_overMax h := Kernel.NockProgramCell.sampleOf_overMax_refused _ _ _ _ h
  overMax_congr agree := Kernel.NockProgramCell.overMax_congr agree
  staleField_names pinned claimed current named changed only :=
    Kernel.NockEntry.staleField_names pinned claimed current named changed only
  door_decode_encode d member state := by
    cases member
    exact Kernel.NockProgramCell.ofJamAtom_jamAtom state
  door_eventOf d member stored event ev := by
    cases member
    show (Noun.cue (Noun.jam _)).bind Kernel.NockEntry.eventOf = some ev
    rw [Noun.cue_jam]
    rfl
  door_pokeInput_injective d member := by
    cases member
    intro stored stored' event event' ev ev' same
    simp only [nockDoor, Kernel.NockEntry.job, Noun.cell.injEq, Noun.atom.injEq, true_and] at same
    obtain ⟨hu, he, hw, hc⟩ := same
    exact ⟨Kernel.NockEntry.ustateNoun_injective hu, he, Prod.ext hw hc⟩

theorem nock_toMachine : nock.toMachine = Machine.nock := rfl

/-- **`sampleOf_injective`** (EVAL §1.1's corollary, on any evaluator): the generic record
is injective in what it reads (`sampleRecord_injective`), and the evaluator's encoding is
injective under the layout (`encodeSample_injective`). -/
theorem sampleOf_injective (E : Evaluator) {abi : Abi} {ctx ctx' : Context}
    {targets targets' : List Nat} {read read' : Nat → String → Option Int} {i : E.Input}
    (h : E.sampleOf abi ctx targets read = some i) (h' : E.sampleOf abi ctx' targets' read' = some i) :
    Kernel.NockProgramCell.contextOf abi.context ctx = Kernel.NockProgramCell.contextOf abi.context ctx' ∧
      targets = targets' ∧ ∀ slot ∈ abi.sample, read slot.target slot.slot = read' slot.target slot.slot := by
  obtain ⟨s, hs, he⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨s', hs', he'⟩ := Option.bind_eq_some_iff.mp h'
  exact Kernel.NockProgramCell.sampleRecord_injective hs (E.encodeSample_injective he he' ▸ hs')

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

/-! ## Resolution: a record's evaluator against the registry

Moved below the kernel's run (E3) so that a record's BIRTH is refused by the same function
that refuses its run (`Kernel.Run.resolve` maps this one into the run's refusals). -/

/-- Why a record's evaluator id does not resolve. -/
inductive Unresolved where
  /-- No compiled-in entry has the id. -/
  | unknownEvaluator
  /-- The entry is compiled in and this deployment's operator disabled it. -/
  | evaluatorDisabled
  deriving DecidableEq, Repr

def resolve (disabled : List Digest) (id : Digest) : Except Unresolved Evaluator :=
  match registry.find? (fun E => decide (E.id = id)) with
  | none => .error .unknownEvaluator
  | some E => if E.id ∈ disabled then .error .evaluatorDisabled else .ok E

/-- **`resolve_registered`**: what `resolve` admits is a compiled-in entry with
exactly the named id, not disabled. Never friend-extensible. -/
theorem resolve_registered {disabled : List Digest} {id : Digest} {E : Evaluator}
    (h : resolve disabled id = .ok E) :
    E ∈ registry ∧ E.id = id ∧ E.id ∉ disabled := by
  unfold resolve at h
  split at h
  · cases h
  · rename_i found hf
    split at h
    · cases h
    · rename_i enabled
      cases h
      exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, enabled⟩

theorem resolve_unknown {disabled : List Digest} {id : Digest}
    (absent : ∀ E ∈ registry, E.id ≠ id) : resolve disabled id = .error .unknownEvaluator := by
  unfold resolve
  rw [List.find?_eq_none.mpr (by intro E m; simpa using absent E m)]

/-- Pole: an id that is not Nock's is refused `unknownEvaluator`, whatever is disabled. -/
theorem pole_unknownEvaluator (disabled : List Digest) (id : Digest) (other : id ≠ nock.id) :
    resolve disabled id = .error .unknownEvaluator :=
  resolve_unknown (by
    intro E m
    simp only [registry, List.mem_singleton] at m
    subst m
    exact fun same => other same.symm)

/-- The refusal pole is inhabited: of the ids 0 and 1, at least one is not Nock's. -/
theorem unknownEvaluator_inhabited (disabled : List Digest) :
    ∃ id, resolve disabled id = .error .unknownEvaluator := by
  by_cases zero : nock.id = ⟨0⟩
  · exact ⟨⟨1⟩, pole_unknownEvaluator disabled _ (by rw [zero]; simp)⟩
  · exact ⟨⟨0⟩, pole_unknownEvaluator disabled _ (Ne.symm zero)⟩

theorem nock_found : registry.find? (fun E => decide (E.id = nock.id)) = some nock :=
  List.find?_cons_of_pos (decide_eq_true rfl)

/-- Pole: Nock's id resolves to Nock unless the operator disabled it. -/
theorem pole_nock_resolves (disabled : List Digest) (enabled : nock.id ∉ disabled) :
    resolve disabled nock.id = .ok nock := by
  unfold resolve
  rw [nock_found]
  exact if_neg enabled

/-- Pole: disabled by the operator, Nock is refused `evaluatorDisabled`. -/
theorem pole_evaluatorDisabled (disabled : List Digest) (off : nock.id ∈ disabled) :
    resolve disabled nock.id = .error .evaluatorDisabled := by
  unfold resolve
  rw [nock_found]
  exact if_pos off

/-- The only evaluator anything resolves to today is Nock. -/
theorem resolve_nock {disabled : List Digest} {id : Digest} {E : Evaluator}
    (h : resolve disabled id = .ok E) : E = nock := by
  have := (resolve_registered h).1
  simpa [registry] using this

end Evaluator

/-! ## Admission at birth: the record against its evaluator (E3) -/

/-- **The store-free birth check of a record on its evaluator**, in refusal order: the
code decodes and is canonical; the ABI is this version; NO NAME holds a NUL (the ABI
decoder's rule, `nulInName`); the fuel is positive; the params decode (`paramsMalformed`)
and pass the evaluator's own check; the ABI's shape. The params it returns are the ones
the kernel runs with. -/
def Machine.admit (M : Machine) (program : Program) : Except NockProgramCodec.Refusal M.Params :=
  if (M.decode program.jam).isNone then .error .noCue
  else if M.canonical program.jam = false then .error .nonCanonical
  else if program.abi.version ≠ abiVersion then .error .abiVersion
  else if ¬ NamesNulFree program.abi then .error .nulInName
  else if program.abi.fuel = 0 then .error .fuelZero
  else match M.decodeParams program.params with
    | none => .error .paramsMalformed
    | some params =>
      match M.checkParams params with
      | some reason => .error reason
      | none => if AbiShape program.abi then .ok params else .error .abiShape

/-- **`admit_ok`**: an admitted record decodes and is canonical, carries this ABI version, NO
NUL in any name, a positive fuel, params that decode (to what it returns) and pass the
evaluator's check, and a well-shaped ABI. -/
theorem Machine.admit_ok {M : Machine} {program : Program} {params : M.Params}
    (h : M.admit program = .ok params) :
    (M.decode program.jam).isSome ∧ M.canonical program.jam = true ∧
      program.abi.version = abiVersion ∧ NamesNulFree program.abi ∧ 0 < program.abi.fuel ∧
      M.decodeParams program.params = some params ∧ M.checkParams params = none ∧
      AbiShape program.abi := by
  unfold Machine.admit at h
  split at h; · cases h
  rename_i hcue
  split at h; · cases h
  rename_i hcanon
  split at h; · cases h
  rename_i hver
  split at h; · cases h
  rename_i hnul
  split at h; · cases h
  rename_i hfuel
  split at h
  · cases h
  · rename_i decoded hdec
    split at h
    · cases h
    · rename_i hcheck
      split at h
      · rename_i shape
        cases h
        refine ⟨by cases hd : M.decode program.jam <;> simp_all, by simpa using hcanon, by simpa using hver, by simpa using hnul,
          by omega, hdec, hcheck, shape⟩
      · cases h

/-- **`admit_nulInName`** (E3, the ABI decoder's rule): a record whose code is well formed and
whose ABI is this version, but one of whose names holds a NUL, is refused `nulInName` — before
its fuel, its params or its shape are read. -/
theorem Machine.admit_nulInName {M : Machine} {program : Program}
    (cues : (M.decode program.jam).isSome) (canonical : M.canonical program.jam = true)
    (version : program.abi.version = abiVersion) (nul : ¬ NamesNulFree program.abi) :
    M.admit program = .error .nulInName := by
  have hcue : (M.decode program.jam).isNone = false := by simpa using cues
  unfold Machine.admit
  simp [hcue, canonical, version, nul]

theorem Machine.admit_noCue {M : Machine} {program : Program} (bad : M.decode program.jam = none) :
    M.admit program = .error .noCue := by
  unfold Machine.admit; simp [bad]

theorem Machine.admit_nonCanonical {M : Machine} {program : Program}
    (cues : (M.decode program.jam).isSome) (bad : M.canonical program.jam = false) :
    M.admit program = .error .nonCanonical := by
  have hcue : (M.decode program.jam).isNone = false := by simpa using cues
  unfold Machine.admit; simp [hcue, bad]

theorem Machine.admit_fuelZero {M : Machine} {program : Program}
    (cues : (M.decode program.jam).isSome) (canonical : M.canonical program.jam = true)
    (version : program.abi.version = abiVersion) (names : NamesNulFree program.abi)
    (zero : program.abi.fuel = 0) : M.admit program = .error .fuelZero := by
  have hcue : (M.decode program.jam).isNone = false := by simpa using cues
  unfold Machine.admit; simp [hcue, canonical, version, names, zero]

namespace Evaluator

/-- **`admitRecord`**: what a birth of this record meets, store-free: its evaluator resolves
(`unknownEvaluator`, `evaluatorDisabled`), and the record passes that evaluator's `admit`. -/
def admitRecord (disabled : List Digest) (program : Program) : Except NockProgramCodec.Refusal Unit :=
  match resolve disabled program.evaluator with
  | .error .unknownEvaluator => .error .unknownEvaluator
  | .error .evaluatorDisabled => .error .evaluatorDisabled
  | .ok E =>
    match E.admit program with
    | .error reason => .error reason
    | .ok _ => .ok ()

/-- The registry's cell law for a program record (profile-free: nothing disabled): it names a
compiled-in evaluator and passes its `admit`. -/
def RecordAdmissible (program : Program) : Prop := (admitRecord [] program).toBool = true

instance recordAdmissibleDecidable (program : Program) : Decidable (RecordAdmissible program) := by
  unfold RecordAdmissible; infer_instance

/-- **`admitRecord_unknownEvaluator`** (E3, at birth): a record naming an id no compiled-in
evaluator has is refused `unknownEvaluator`, whatever it holds. -/
theorem admitRecord_unknownEvaluator {disabled : List Digest} {program : Program}
    (absent : ∀ E ∈ registry, E.id ≠ program.evaluator) :
    admitRecord disabled program = .error .unknownEvaluator := by
  unfold admitRecord; rw [resolve_unknown absent]

/-- **`admitRecord_evaluatorDisabled`** (E3, at birth): a record on an evaluator this
deployment disabled is refused `evaluatorDisabled`, whatever it holds. -/
theorem admitRecord_evaluatorDisabled {disabled : List Digest} {program : Program}
    (nockRecord : program.evaluator = nock.id) (off : nock.id ∈ disabled) :
    admitRecord disabled program = .error .evaluatorDisabled := by
  unfold admitRecord; rw [nockRecord, pole_evaluatorDisabled disabled off]

/-- The admitting pole: a record on an enabled evaluator is exactly as admissible as that
evaluator's `admit` says. -/
theorem admitRecord_resolved {disabled : List Digest} {program : Program} {E : Evaluator}
    (resolved : resolve disabled program.evaluator = .ok E) :
    admitRecord disabled program = (E.admit program).map fun _ => () := by
  unfold admitRecord; rw [resolved]
  simp only
  cases h : E.admit program <;> simp [Except.map]

-- Concrete admission fixtures and their kernel-decided poles live in
-- `Assurance.EvaluatorAudit`, required by Deployed and Assurance.

def refusalOf {α : Type} : Except NockProgramCodec.Refusal α → Option NockProgramCodec.Refusal
  | .error reason => some reason
  | .ok _ => none

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
/-- info: 'Minidregg.Compiler.Evaluator.resolve_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolve_registered
/-- info: 'Minidregg.Compiler.Evaluator.pole_unknownEvaluator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_unknownEvaluator
/-- info: 'Minidregg.Compiler.Evaluator.pole_nock_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_nock_resolves
/-- info: 'Minidregg.Compiler.Evaluator.pole_evaluatorDisabled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pole_evaluatorDisabled
/-- info: 'Minidregg.Compiler.Evaluator.admitRecord_unknownEvaluator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admitRecord_unknownEvaluator
/-- info: 'Minidregg.Compiler.Evaluator.admitRecord_evaluatorDisabled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms admitRecord_evaluatorDisabled
/-- info: 'Minidregg.Compiler.Evaluator.sampleOf_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sampleOf_injective

end Evaluator

/-- info: 'Minidregg.Compiler.Machine.nock' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Machine.nock

end Minidregg.Compiler
