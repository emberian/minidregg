# Objective Bend Core4: proof-engineering target structure

Lane PROOF-ENG, 2026-10-04. Scope: `Theory/ObjectiveBend*` (definition modules in the
default build; proof modules in the `ObjectiveProofs` target). Evidence tags: READ = read
at source, MEASURED = counted in this clone, DESIGN = this note's decision.

## 0. What makes a new constructor expensive (READ/MEASURED)

* **Positional recursors.** `Theory/ObjectiveBendDemandPreservation.lean` runs
  `refine PartialTyping.rec (motive_1 := …) (motive_2 := …) (motive_3 := …) ?_ … ?_ source`
  fourteen times, each with 29 positional `?_` and 29 positional bullets. Most are
  inversion lemmas where one or two constructors matter and the rest are
  `intros; trivial`. A new typing rule means inserting a bullet at the right
  *position* in all fourteen, including the ~twelve where it is irrelevant.
* **Replicated step trees.** `graph_stepRaw`, `graph_stepRaw_names`,
  `graph_stepRaw_safety_names` (Adequacy), `graph_stepRaw_whole` (Completeness) and
  `typed_stepRaw_preserved` (Preservation) each re-spell the same nested
  `cases control / cases term / cases stack / cases frame` tree that `stepRaw` has. The
  per-case lemmas already exist (`typed_enter_preserved`, `graph_enter_suspended`, …);
  what does not exist is a *shared* case split.
* **Dispatcher beside the definitions.** The dispatchers live in the same file as the
  invariant's definitions (`GraphRepresents`, `SourceDispatch`), so a per-constructor
  file cannot be imported by the dispatcher without importing back into the
  definitions: the cycle the sums lane recorded (SUMS-DESIGN §10: "graph_stepRaw must
  call the new per-constructor lemmas, which need Adequacy's own definitions").

## 1(a). Per-constructor case modules

**Layout (DESIGN)**, per proof module `M` (Preservation first, then Adequacy):

```
Theory/ObjectiveBend<M>/Base.lean        definitions + shared lemmas (no dispatcher)
Theory/ObjectiveBend<M>/Cases/<Group>.lean  per-constructor case lemmas; import Base only
Theory/ObjectiveBend<M>.lean             the dispatchers + corollaries + pins; imports Cases/*
```

The cycle is broken by construction: a case file imports `Base` (definitions), never the
dispatcher; the dispatcher file imports every case file. A case that needs another
*induction's* result (e.g. `typed_case_preserved` uses `source_insert_binding`) imports the
case file that proves it; the import graph is a DAG because inductions never call the
step dispatcher. Every declaration keeps its name and namespace; consumers keep
importing `Theory.ObjectiveBend<M>` (now the umbrella of its pieces). The statement
snapshot (§1d) is keyed by declaration name, so the move is checked.

**Mechanism for the step dispatchers (DESIGN): `StepCases`, a structure of named case
obligations, assembled once.** In a definitions-level module (it mentions only
`State`/`Control`/`Term`/`Frame`):

```lean
structure StepCases (P : State → Prop) : Prop where
  enter      : ∀ s address, s.control = .enter address → P s
  bound      : ∀ s index env, s.control = .evaluate (.bound index) env → P s
  …          -- one field per Term constructor, per Frame constructor, per terminal control
  return_ifBool : ∀ s value t f env rest, s.control = .returned value →
                    s.stack = .ifBool t f env :: rest → P s
theorem StepCases.apply {P} (cases : StepCases P) (s : State) : P s  -- the only case tree
```

Each dispatcher becomes `StepCases.apply { enter := …, bound := …, … } state`: a
structure instance with one named line per constructor. Adding a constructor = one
field + one line of `StepCases.apply` (written once for all five dispatchers); each
dispatcher then fails with *"fields missing: `newCtor`"*, naming the obligation instead
of a positional mismatch. Chosen over (i) Lean's generated `stepRaw.fun_cases` (its
cases are numbered `case1…caseN`, positional again, and shift when a constructor is
added) and (ii) a `match` per dispatcher (what exists now: five copies of the tree).

**Mechanism for derivation inductions (DESIGN): tagged goals + a default closer.**
`apply PartialTyping.rec (motive_1 := …) (motive_2 := …) (motive_3 := …) (t := source)`
leaves one goal *per constructor, tagged with the constructor's name* (the recursor's
minor-premise binder names). The proof then reads

```lean
  apply PartialTyping.rec (motive_1 := …) (motive_2 := …) (motive_3 := …) (t := source)
  case bound => …
  case conversion => …
  all_goals objective_trivial     -- §1b; every irrelevant constructor
```

so a new constructor costs nothing where it is irrelevant, and where it is relevant the
error names `case newCtor`. When a case is long (`source_insert_binding` has 29
substantive cases), its body moves into a lemma `source_insert_binding.case_<ctor>` in
that constructor's case file; the induction closes those goals with
`objective_cases source_insert_binding`, which resolves each goal's tag `c` to the
constant `source_insert_binding.case_c`. A new constructor's case lemma then lives in
its own file and the induction's text does not change at all.

## 1(b). Automation (DESIGN; measured in §4 on two existing cases)

* `@[objective_step]` simp set: the `stepRaw` equations specialised per control/frame
  (`stepRaw_enter`, `stepRaw_evaluate_bound`, …) plus `forcingShared`/`allocateFields`
  unfolding — `simp only [objective_step, h]` replaces the recurrent
  `simp [stepRaw,control,found,ResultControl]` spelling.
* `objective_trivial`: `intros; first | trivial | (simp only [immediateValue, scalarValue] at *; done) | simp_all`
  — the closer for the irrelevant cases of an inversion.
* `objective_cases X`: closes each remaining goal tagged `c` by `exact X.case_c` with
  the goal's local context (`intros` first).

## 1(c). Pins

`Theory/AssertAxioms.lean` already defines `#assert_axioms foo` (refuses `sorryAx`,
compiler trust, project axioms) but imports `Mathlib.Tactic.Basic`, and the Objective
modules import only `Lean`. DESIGN: move the command into a core module
`Theory/AxiomPin.lean` (`import Lean`), widen it to `#assert_axioms n₁ n₂ …` (reporting
every offender), and re-export it from `Theory.AssertAxioms` (no consumer changes). The
402 hand-typed `#guard_msgs in #print axioms` pins in `Theory/ObjectiveBend*` become one
`#assert_axioms` line per section. The *exact* axiom set per declaration — the only
information the hand-typed text carried beyond "within the standard three" — moves to
the generated index `scripts/gates/objective-axioms.pin` (§1d), which covers every
declaration, not the 402 someone remembered.

## 1(d). Statement-stability gate

`scripts/ObjectiveSnapshot.lean` (imports `ObjectiveProofs`) prints one line per
non-generated declaration whose module starts `Theory.ObjectiveBend`: kind, name,
elaborated type pretty-printed with `pp.fullNames` at unbounded width (whitespace
collapsed), and for `Prop`-valued definitions their body (a hypothesis's meaning *is* its
body). A second file lists each theorem's exact axiom set. The checked-in copies are
`scripts/gates/objective-statements.snapshot` and `scripts/gates/objective-axioms.pin`.
An *announced* change is a commit that regenerates them (`--update`); any other
difference fails. The elaborated type, not the source text, is compared: a
reformatting is not a change, a changed premise is.

## 1(e). Vacuity gates (HypothesisLedger)

**Why not literally "REFUTED when any instance refutes" (DESIGN, MEASURED).** On the
10-04 ledger (persvati `ledger-c2.out`), 25 GREEN assumption-tier families — e.g.
`MaskedOpeningHiding` (refuted at an F₅ triple), `SeamOk`, `IConfluent` — are refuted at
an instance *by design*: a floor must be satisfiable and refutable (Prove-the-floor-FALSE
doctrine). A family-level any-instance rule turns all 25 red.

**Rule shipped: a refutation COVERS a consumer.** A consumer binding `D a⃗` is VACUOUS
when some proved refutation `¬ D b⃗` (general or instance) unifies with it, the
refutation's variables as metavariables and the consumer's as rigid: the consumer is
true of nothing at exactly the point it assumes. A family with a covered consumer is
RED, whatever its tier. Second rule: an assumption with a refuting instance and **no**
satisfying instance is REFUTED-ONLY and can no longer be allowlisted as TOOTHLESS (the
un-fixed Polishchuk–Spielman sat in the allowlist as TOOTHLESS).

**Trivial-inhabitant probe.** For every structure we own that a theorem binds and that
carries a proof field: fill its predicate fields with `fun … => True` (then
`fun … => False`), its `Option`-valued fields with `none`, other data with `default`,
and try to close the proof fields with a fixed tactic battery, *for all parameters at
once*. Success = TRIVIAL: the structure certifies nothing by itself. RED for the
assumption tier, reported for the rest.

**Regression plants** (instrument teeth, checked every run): the un-fixed
Polishchuk–Spielman statement verbatim with its `ZMod 5` consumer and the real
refutation `Selvage.PolishchukSpielmanRefutation.polishchukSpielman_unfixed_false_F5`
must read VACUOUS; a `PackedRefinement`-shaped structure over `stepRaw`'s `Macrostep`
must read TRIVIAL; a codec-shaped structure with a totality obligation must not.

## 1(f). Gate

`scripts/check-objective-proofs.sh`, a `local-gates.sh` gate `objective-proofs`:
`lake build ObjectiveProofs`; the snapshot diff (self-tested: a planted statement change
must turn it red); the preview cohort (`tests/objective-bend-source/check-preview.ts`);
translation validation (`native/bend-source/objective-elaborate-tv.ts`); the C differential
(`native/objective-emit/differential.py` over `packets.ts`). `bun` is required (`BUN=`);
absent → the gate is RED, never skipped.

## Order of work

(c)(d)(f) first — cheap and protective; then (e); then (a)+(b) on Preservation as the
proof of method, statements fixed by (d); then Adequacy's graph lemmas.
