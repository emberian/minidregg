# EVAL: the kernel referees programs on any registered evaluator

This is the present-state description of K-EVAL: the layer that makes the run check of
`docs/NOCK.md` independent of Nock. The Lean modules are the authority; this document says what
they do and where they are. Section numbers are kept from the design of 2026-10-01 so that the
`EVAL §N` citations in `Compiler/Evaluator.lean`, `Compiler/NockProgramCodec.lean`,
`Kernel/Door.lean`, `Kernel/Run.lean`, `Kernel/NockProgramCell/Sample.lean`, `Pred/Core.lean`,
`Pred/Satisfiable.lean`, `Host/LawSat.lean`, `Theory/Eval.lean`, `Theory/NockCost.lean` and
`native/resource-client/journey.d/jeval.sh` resolve here. Lane names (K-EVAL, E1 to E4, C-SAT,
NC-1, NC-2) are listed in §7.

Each section is marked **shipped** (in `main`, with the module named), **changed** (shipped, but
not as first designed: the difference is stated) or **design** (not built).

## 0. Summary

`Compiler.Evaluator` states what an evaluator must bring for the kernel to referee its runs by
re-execution: a machine, its byte forms, the kernel's entry into a run, and the theorems that
make the run's answer a verdict about the term. `registry := [nock]`; adding an evaluator is
adding a term there, and a missing theorem is a build failure. A program record names its
evaluator, and `programId` covers that name. The kernel resolves the record's evaluator against
the registry at birth and at every run, and an operator may disable a compiled-in evaluator per
deployment. Nock is the only registered evaluator. No second evaluator (SKI, PLAN) is built.

## 1. The kernel is evaluator-agnostic

### 1.1 The interface. **Changed.**

`Compiler/Evaluator.lean`. The data is `Machine`; the facts are `Evaluator extends Machine`.
The referee's functions take a `Machine`, so a decided pole on Nock names only data.

- **Machine**: `name`, `semantics`; `Term`, `Output`, the fueled `run : Nat → Term → Except
  Outcome Output` and the metered `steps`; `Code`, `decode`, `canonical`; `Input`,
  `encodeInput`, `encodeOutput`; the byte entry point (`decodeTerm`, `encodeTerm`, `runBytes`,
  `exportFn`); `Params` with `encodeParams`, `decodeParams`, `checkParams`; the kernel's run
  (`entry`, the single-pass `oracle`, `writesOf`); the sample (`encodeSample`, `overMax`,
  `staleField`); and `door : Option EvalDoor` (§4).
- **Evaluator** adds `Spec` and `Crash` and the facts: `run_sound`, `run_complete`,
  `spec_deterministic`, `run_crash_iff`, `crash_not_spec`, `run_fuel_monotone`,
  `steps_stable`, `exhausted_says_nothing`, `canonical_unique`, the injectivity of the input
  and output encodings, the byte entry point's soundness and `export_is_run`, the oracle's three
  outcomes and `oracle_is_export`, the params round trip and `decodeParams_canonical`,
  `encodeSample_injective`, the sample-slot facts, and the door facts.
- `exhausted_says_nothing` is required: an evaluator must exhibit a term that has a value and
  still runs out of fuel. An interpreter that reports exhaustion as a failure of the term
  (`Theory.EvmFragment`) cannot be registered.
- **The sample record** (`Kernel.NockProgramCell.Sample`: context, target ids, `(key, value)`
  per ABI slot) is built by `sampleRecord` and encoded by each evaluator under the ABI's layout.
  `Evaluator.sampleOf_injective` is a corollary of `sampleRecord_injective` and
  `encodeSample_injective`.

Changed from the design: one `Term` type (Nock's is the pair `(subject, formula)`) instead of
separate `Program`/`Input` arguments to `Spec` and `run`. `run` returns the output only; the
count is the separate `steps`, and the kernel's `oracle` returns `Theory.Eval.Ran`, which keeps
the count on a crash and on exhaustion. The design's `Except Outcome (Output × Nat)` would drop
that count, which the refusals `crash k` and `exhausted k` report (`Theory/Eval.lean`). The id is
`idOf name semantics`, cSHAKE256 under `DREGG.EVALUATOR/v1`.

### 1.4 The refactor. **Changed.**

1. **Registry.** `Compiler.Evaluator.registry := [nock]` (`registry_ids_distinct`,
   `nock_registered`). `identities` also lists `objective-core4`, the evaluator Objective Bend
   admission re-executes; it is not a program-record referee (no record can name it) but an
   operator can name and disable it. `resolve` refuses `unknownEvaluator` or
   `evaluatorDisabled` (`pole_unknownEvaluator`, `pole_evaluatorDisabled`).
2. **The program record names its evaluator.** `NockProgramCodec.Program` is `{evaluator, jam,
   abi, params}` under the frame `DREGG/PROGRAM/v1`; `programId` covers all four, so the same
   bytes under another evaluator are another program. The `DREGG/NOCK/PROGRAM/v1..v3` frames do
   not decode (`program_old_frame_refused`). The arm moved from the ABI to Nock's params
   (`DREGG/NOCK/PARAMS/v1`). `admitRecord` refuses an unknown or disabled evaluator at birth.
3. **The law atom stays `ran P`.** The controller also projects `run/evaluator/<id> = 1`
   (`Pred.evaluatorSlot`), so a room law may pin an evaluator with `eq`.
4. **`Kernel/Run.lean`** is the run check with the evaluator threaded through: `checkRun`,
   `runOf`, `checkRun_sound` over `E.Spec`, and the same theorems at Nock (`docs/NOCK.md` §3.3).
5. **The sample record** as in §1.1.
6. **Doors** as in §4.

Changed from the design: the files kept their Nock names (`Compiler/NockProgramCodec.lean`,
`Kernel/NockProgramCell.lean`) and the registry kind is still `nockProgram`. Disabling an
evaluator is a deployment parameter (`Profile.disabledEvaluators`, committed in the runtime
profile, set in the genesis params), not a system-cell transition.

## 2b. The law calculus

### 2b(b) Is a law satisfiable? **Shipped (C-SAT).**

`Pred/Satisfiable.lean`. A law's arithmetic atoms (`eq`, `le`, `memberOf`, `writeOnce`,
`monotone`, `eqSlots`, `leSlots`, `leSlotsOff`) are difference constraints over `Int` slots.
`Pred.difference?` translates a law in that fragment to a disjunction of constraint systems
(capped at `dnfCap`); `sumEq`, `witnessed`, `hashEq` and `ran` are outside it. `DiffProblem.decide`
runs Bellman–Ford per system and answers a witness step that `eval` accepts (`witness_sound`) or
a certificate of a negative cycle or a presence clash for every system (`certificate_unsat`,
via `difference_faithful`). The falsifier `allL [le f/1 0, monotone f/1, eq f/1 1]` is decided
unsatisfiable; without the `eq` it admits a step (`Minidregg.Pred.Sat.Sample`). Host op 150
`law-sat` (`Host/LawSat.lean`) serves it; the shell's `law check` and `can --any` ask it
(`native/resource-client/src/lawsat.rs`).

Changed from the design: completeness is a checked certificate, not a `witness_complete`
theorem about the solver. The scope's size ceiling is `Scope.perRequestBytes` (it was
`maxCost`): every signed request's `cost` is an encoded length. The theorem
`step_allowance_nonincrease` is **design**.

## 3. Cost in the types. **Partly shipped.**

`Theory/NockCost.lean` (NC-1) and `Theory/NockCost/Summaries.lean` (NC-2). A `Shape` describes a
set of subjects; `cost sh f` is a step bound for formula `f` on every subject of shape `sh`, or
`none` outside the fragment. `cost_sound`: on every subject of the shape, a run with at least
`B` fuel does not exhaust and its count is at most `B`; `cost_sound_at_bound` is the design's
form at fuel exactly `B`. `costSym` summarises the stdlib's loops so that a bound over values in
the millions is computed without unrolling. On forge the bound equals the measured count, 1,345
(`pole_forge_sym_bound`). A sample slot may declare a maximum (`SampleSlot.max`, refusal
`fieldOverMax`), which gives the program a declared shape (`shapeOf`).

**Design:** the kernel does not consume the bound. There is no `run/bound` slot, no typed surface
language (`bound_sound`, NC-3) and no refusal before cue.

## 4. Doors, evaluator-generic. **Shipped (E4).**

`Compiler.Evaluator.EvalDoor` and `Kernel/Door.lean`. An instance is an ordinary declared object
whose state (as `encodeState` gives it) and event number live in the two fields the ABI's door
record names, on the command's target 0. A poke is one invocation carrying a `RunClaim` whose
sample is `pokeInput (stored state, event + 1, event)` and whose output is `claimOutput
(effects, next state)`. The evaluator brings boot + poke (`poke`), peek (`peek`, at the ABI's
peek arm on a path) and load (`load`, the state now), the state codec, `eventOf`, `product` and
`effects`. The codec's round trip is an `Evaluator` fact (`door_decode_encode`). Generic
theorems: `door_poke_sound`, `door_state_stale_refused`, `door_other_state_stale`,
`door_poke_deterministic`, `door_peek_pure`, `door_load_deterministic`. Nock's door is
`Compiler.Evaluator.nockDoor`; its instance is `Kernel/NockDoor.lean` (`docs/NOCK.md` §2.7). A
door ABI under an evaluator with no doors is refused `doorUnsupported`.

Changed from the design: `poke` is one term (boot, re-install, slam) rather than separate `boot`
and `pokeSpec` fields, and `eventOf` recovers the event from a claim's bytes. Upgrading a door to
a new kernel is **design**.

## 7. Lanes

| lane | what it built | status |
|---|---|---|
| E1 | `Machine`, `Evaluator`, `Evaluator.nock`, `registry` | shipped (`Compiler/Evaluator.lean`) |
| E2 | `Kernel/Run.lean` generic over the evaluator; `run/evaluator/<id>`; `Kernel/NockEntry.lean` | shipped |
| E3 | the program record `DREGG/PROGRAM/v1`, params, `admitRecord`, the generic sample record | shipped, files keep their Nock names |
| E4 | generic doors | shipped (`Kernel/Door.lean`) |
| C-SAT | law satisfiability, op 150, `can --any` | shipped (§2b(b)) |
| NC-1, NC-2 | `cost`, `cost_sound`, loop summaries, `SampleSlot.max` | shipped (§3) |
| NC-3 | typed surface language, `run/bound` | design |
| SKI, PLAN, MASK, DIFF-E | a second evaluator, `step_depends_only_on_read_axes`, an evaluator-parametric differential | design |

Journey: J-EVAL (`journey.d/jeval.sh`). Two Stores from two genesis params files, one disabling
`nock`. A record naming an unregistered evaluator is refused at the check and at birth; on the
Store that disables `nock`, forge's record is refused `evaluatorDisabled` at the check and at
birth; a law pinning `run/evaluator/<nock>` admits forge's run, and one pinning another id
refuses it.
