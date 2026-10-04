# ZK: when Mini may admit by proof, and what a verified Objective proof establishes today

**Today Mini admits by proof: never.** Every Objective invocation is admitted by
re-execution. The receiver runs the checked source with `runBounded` under the signed
envelope's limits and budget, and `admitted_source_semantics`
(`Kernel/ObjectiveBendAdmissionSemantics.lean`) states what the admitted output is in source
terms. No proof carrier gates any effect. The predicate atom `witnessed` lowers to the
constant indicator 0 (`Compiler/PredCompile.lean`, `lowerA (.witnessed _) = (cst 0, [])`), so
no law that names a proof can pass.

This document has two parts:

- Part 1 is the bar a proof carrier must clear before that changes. It was written before any
  carrier exists, so it cannot be fitted to one.
- Part 2 says, link by link, what a verified proof of an Objective run implies today. It also
  names the Lean that establishes each link.

Evidence classes: **compiled** means a named Lean module built in the lane `zk-truth`
(persvati `claude-lanes/zk-truth/logs/*.log`, cited per module). **Authored** means written
and not built. **Executed** means run against live state. Nothing here is integrated or
deployed. The source of the bar is the scholar document `claudesplosion/planning/ZK.md` §2
(2026-10-01, cv `01a0f6ae`). This file is its in-repo statement, adapted to the Objective
proof path that exists after the cut.

---

## Part 1. The admission bar

A carrier that fails any clause may still be **observe-only**. Its verdict is then logged
beside the re-execution verdict and gates nothing.

### B1. A theorem gives the bound in bits of work, at the parameters that run

The carrier needs a Lean theorem of this shape. Its adversary is quantified, and it uses one
game on one coin:

```lean
theorem carrier_sound (Q : ℕ) (A : Adversary Q) :
    Pr[(x, π) ← A ; verify params x π = true ∧ ¬ Holds x] ≤ ε params Q
theorem carrier_bits       : ∀ Q ≤ 2 ^ k,     ε params Q ≤ Q / 2 ^ k
theorem carrier_bits_tight : ¬ ∀ Q ≤ 2 ^ (k+1), ε params Q ≤ Q / 2 ^ (k+1)
```

- `params` is the literal record that the verifier is called with.
- `ε` sums every leg in one game: the field/algebraic leg, queries, the commit phase,
  Fiat–Shamir, grinding, and the hash's collision term as a function of `Q`. The legs are
  added, not reported as a minimum across columns.
- The regime must be proven. Unique decoding qualifies. Johnson qualifies only once its
  agreement theorem for that exact code, domain and fold arity is in the tree. Capacity never
  qualifies.
- The bound must be two-sided (`carrier_bits_tight`), because a one-sided `≤` is satisfied by
  every loose bound.

### B2. The statement is audited for what it binds

The audit is a written artifact with one line per check. Its reviewer is not its author.

| # | check |
|---|---|
| 1 | The `verify` in the theorem **is** the function the kernel invokes: a Lean `def` the Host calls, or its `@[export]`. A model beside the code does not count. No `@[extern]` may sit on the path from bytes to verdict. |
| 2 | `Holds x` is the kernel's own semantic object. For an Objective run, it is the conclusion of `admitted_source_semantics`: a finished `runBounded` run of the admitted term at the envelope's limits, whose result is a deep source evaluation. |
| 3 | The kernel builds the statement `x` from its own state and the signed claim: source and input identities, the envelope, the layout and the output codec. The proof bytes carry no statement and no parameter. In particular, no size, height, round count, query count or **tick count** is read from the proof (B8). |
| 4 | **Premise inhabitation at the deployed parameters.** The build checks a true `x` with an accepted `π`, produced by the real pipeline. |
| 5 | **Teeth.** A false `x` is rejected. A mutation harness flips each proof field, asserts that the bytes changed, and requires the verdict to flip. |
| 6 | Every hypothesis of `carrier_sound` is listed with its poles: satisfiable, refutable, and attempted both ways at the deployed parameters. |
| 7 | Every carrier, embedding, codec and commitment the theorem quantifies over has been read. There is no identity embedding, no injectivity of a compressing map, and no structure without an inhabitant. For Objective this includes the **state codec**: its decoder is the layout's one decoder (B7). |
| 8 | The perimeter table lists, for each component of `x` and each value the prover computes, who computes it and what constrains it. The `#assert_axioms` output is printed. |

### B3. A credit cap derived from the bound

`perEffectCap$(k) = 2^k / (h · M)`. With the proposed `h = 2^60` hash evaluations per dollar
and margin `M = 2^20`, this gives `2^(k−80)` dollars. Below 80 proven bits, the carrier is
observe-only. At 124 bits and above, the formula stops binding and the aggregate cap binds
instead.

- `move` legs are **never** proof-gated. Value moves only by re-execution.
- The cap is written in the law, beside the atom that names the carrier. A room whose law has
  no cap gets re-execution.
- Each carrier has an **aggregate exposure cap** per window, set by the operator and tracked in
  the system cell. The per-effect cap prices the bound. The aggregate cap prices a bug.

The constants `h` and `M` are ember's to decide (scholar ZK.md §6, D2).

### B4. The carrier slot

A carrier is a Lean value whose fields are its evidence. These are the fields it must have:

- `id`, `params`: pinned at registration, never parsed from a proof.
- `verify : Statement → ByteArray → Bool`: total, written in Lean, and the function the kernel calls.
- `basis`: `exact` (re-execution, with its soundness theorem), `bounded k` (B1), or `bonded`
  (attestation, where the cap is the bond).
- `fires : ∃ x π, Holds x ∧ verify x π = true` (B2.4).
- `refuses : ∃ x π, ¬ Holds x ∧ verify x π = false` (B2.5).
- `assumes`: a list that is empty or contains only standard hash assumptions.

The `prove` evidence constructor is added only by the commit that registers the first
carrier, so it never exists without an inhabitant. Refusals have distinct names:
`carrierUnknown`, `carrierObserveOnly`, `carrierDisabled`, `proofRejected`, `overCap`,
`exposureExceeded` and `valueLegUnderProof`. All of them fail closed.

### B5. Registration

The registry is a Lean list compiled into the Host, so the build fails without the theorem.
At run time:

- the operator may enable or disable a compiled-in carrier and lower its caps;
- a law author may opt a cell in;
- a friend can do neither.

### B6. The journal

Every effect admitted on `prove` evidence is journaled with:

- the carrier id, the params digest, the regime and `k`;
- the cap in force and the value charged against it;
- the statement digest and the proof bytes.

Where the node holds the inputs, `audit` also re-executes and compares. A disagreement flips
the carrier to observe-only.

### B7. Objective: the codec is the layout's one decoder

This clause is new, and comes from Part 2. A proof about the oblivious graph speaks about
bits. The receiver turns bits into a source state with a decoder. That decoder must be **one
function of the public layout and the bits**: `ObjectiveDemandRegions.state layout`. It reads
the state region and every table region (code rows, code fields, names, environments,
records) from the same bits, and no program and no table is supplied beside the bits.

A decoder that reads the code through tables supplied beside the bits fails this clause,
because it is the relation of no refinement at all (`externalTables_not_refinement`, Part 2).
The verifier's public result wires must also be read by this same decoder, which is link 5
below.

### B8. Objective: ticks come from the signed envelope, never from the run

The unrolled graph a proof is checked against is `build original (rate.ticks capacity)`.
`capacity` is the signed claim's envelope (`ObjectiveInvocationClaim.Capacity`, whose
`sourceTicks` the caller declares and the tariff prices). `rate` is the controller's public,
versioned `PhysicalRate`. The receiving statement
`ObjectiveBendCommittedSource.arithmetic_observes_source` takes exactly these two arguments
in place of a free tick count, so a proof unrolled at a measured count does not instantiate
it.

A program that has not completed within the envelope yields no completed row and no
observation. That refusal is public by design, and nothing is refunded. A measured count would
leak: two secrets with the same meaning run for 5 and 8 steps (`measured_view_leaks`, Part 2).

### B9. Privacy profiles additionally need transcript zero knowledge

When the proof's purpose is that the verifier never sees the input, B1 needs a companion: a
zero-knowledge theorem for the deployed transcript, meaning the hiding PCS composed with the
quotient, FRI and adaptive queries, at the deployed height. Padding to a public height alone
hides nothing (`padded_rows_determine_row`, Part 2).

### Today, by this bar

Re-execution gates. Attestation would gate up to a bond, but no attestation carrier exists.
**No proof carrier is admissible.** For the Objective path, B1, B2.1, link 5 of B7 and B9
have no theorem at all. A carrier built today could be registered only as observe-only, never
with a `bounded` basis.

---

## Part 2. What a verified Objective proof implies today, link by link

| # | Link | Status | Where |
|---|------|--------|-------|
| 1 | Native PCS verification ⇒ the arithmetic relation holds for some field assignment | **Not proved.** No theorem connects the native verifier to `BendTraceDirect.lower … Holds`. | — |
| 2 | Arithmetic relation of the graph unrolled at the envelope ticks, with inputs pinned ⇒ an `AcceptedRun` of the per-tick network | Proved (standard axioms). | `BendCommittedUnroll.accepted_run` |
| 3 | `AcceptedRun` + a refinement + `initial` + `readSound` ⇒ `Evaluates source (observationTerm o)` | Proved, conditional on the three premises. Now unrolled at `rate.ticks capacity` (B8). | `ObjectiveBendCommittedSource.arithmetic_observes_source`. **compiled** (`logs/zk5.log`) |
| 4 | A refinement that means something, for a real network | **compiled**: one codec, the layout decoder restricted to certified rows, for five programs on the tranche literal graph | `Assurance/ObjectiveZkLiteralInstance.lean` |
| 5 | The verifier's public result wires are read by the layout decoder | **Not stated anywhere.** | — |
| 6 | Zero knowledge of the transcript | **Not proved.** A one-row disclosure is proved. Padding is shown not to hide. | `Assurance/ObjectiveZkTraceDisclosure.lean` (**compiled**, `logs/trace-disclosure.log`) |

**Does a verified proof imply the source result?** Not end to end, for any program, because
links 1 and 5 are missing.

The strongest statement in the tree (**compiled**) is
`ObjectiveZkLiteralArithmetic.nat7_arithmetic_observes_source`. It quantifies over every
signed envelope, every public rate, and every field assignment satisfying the lowered
constraints of the literal graph unrolled at `rate.ticks capacity`, with the execution inputs
pinned to `.nat 7`'s initial bits. For each of these: if the derived reader answers `o`, then
`Evaluates (.nat 7) (observationTerm o)`. It has no refinement, initial-state or reader
premise. The arithmetic premises remain (`prepared`, `wholeValid`, `inputBounds`,
`inputPinned`, `accepted`, `publicSuccess`).

### The statement audit (`Assurance/ObjectiveZkRefinementAudit.lean`, compiled)

- `PackedRefinement N` is inhabited for **every** network (`packedRefinement_always_inhabited`).
  The administrative stutter accepts any relation closed under "same state". So the structure
  alone certifies nothing.
- With that inhabitant, the receivers' `readSound` forces the free reader to stay silent
  (`trivial_readSound_silent`).
- The corrected form is `PackedCodec`: a functional `decode`, a **derived** reader, and
  `readSound` as a theorem (`PackedCodec.read_sound`). A constant decoder is still a codec that
  never reads (`constantCodec_initial_silent`), so the decoder must be pinned further (B7).

### The code, field and environment regions (`Compiler/ObjectiveDemandLayout`, `ObjectiveDemandRegions`, compiled)

The tranche's input layout is now the state region followed by every table region: code rows,
code field pairs, names (UTF-8 bytes), environments and record fields. The graph
(`ObjectiveDemandLiteralNetwork.network layout`) carries all of them to the next tick.

`ObjectiveDemandRegions.decode layout` reads all of them. It is the only physical result
decoder (`ObjectiveDemandPhysical.result`). `Prepared.initialExact` discharges the initial-state
premise for every prepared program by translation validation: it holds a proof-producing
equality of the decoded complete initial bits with `initial source`.

The corrected refinement statement is `LayoutCodec layout network`: a `PackedCodec` whose
decoder, wherever it answers, **is** `ObjectiveDemandRegions.state layout`. Its results:

- `layoutCodec_binds`: every layout codec reads a prepared program's initial bits, if at all,
  as that program's initial state.
- `layoutCodec_not_foreign`: no layout codec represents `.nat 9`'s bits as `.nat 7`'s initial
  state.
- `regionLayoutCodec` inhabits it.

### The refuter (kept)

`externalTables_not_refinement` concerns the tranche's earlier decoder. That decoder read the
state region against one prepared program's tables, supplied beside the bits. The theorem
states that this relation is the `represents` of **no** `PackedRefinement` of the graph.
`.nat 9`'s bits decode under `.nat 7`'s tables to `initial (.nat 7)`, and one accepted tick
returns `9`. `decoders_disagree` puts both decoders on the same bits.

### The instance (`regionCodec`, compiled)

`certifiedCodec` is general: for any network and decoder, a compiled check over a set of rows
yields a `PackedCodec`. The check requires, for each row, that:

- the decoder succeeds;
- the successor row stays in the set;
- the successor state equals the current state or its `stepRaw` successor, witnessed by the
  proof-producing `ObjectiveDemandStateEquality.state`.

`regionCodec` certifies the union of the reachable rows of `.nat 7`, `.nat 9`, a label, a
Boolean and a closure, with **one** decoder and no program parameter. Non-vacuity comes from the
actual runs of the graph: `nat7_reaches_source_meaning`, `nat9_reaches_source_meaning` and
`label_reaches_source_meaning` (the name is read from the names region).

The scope is per run and per certified set. This is not the universal controller refinement.

### Core4 coverage of the tranche (compiled)

The tranche now represents every Core4 constructor:

- `ObjectiveDemandCode` and `ObjectiveDemandPackedCode`: rows 18–22 cover `inject`, `case`,
  `ifBool`, `perform` and `done`. The primitive field is 3 bits, because the tranche now has
  `labelEqual`.
- `ObjectiveDemandStorage` and `ObjectiveDemandStateCodec`: the `variant` value, the `case` and
  `ifBool` frames, the `yielded` control, and the `missingArm` and `sharedEffect` refusals.
- `ObjectiveDemandStateEquality` and `ObjectiveTermEquality`: all of the above.

The literal graph still dispatches only literals and lambda. Every other opcode returns
handled = false.

### The step-count leak and the envelope fix (`Assurance/ObjectiveZkStepTariff.lean`, compiled)

- Let `plan s := ifZero (nat s) (nat 0) ((λ_. 0) 0)`. Both secrets mean `0`
  (`plan_same_meaning`). Their step counts are 5 and 8 (`plan_steps`).
- `measured_view_leaks`: a public tick count chosen from the measured run differs between the
  two secrets.
- `tariffView_eq_of_within`: under a signed envelope, any two programs that complete within it
  have equal public views. The reason is that completion is a fixed point of `stepRaw`
  (`rawRun_complete_absorbing`).
- `nat7_envelope_run`: for every rate and envelope with `2 ≤ rate.ticks capacity`, the actual
  graph has an accepted run of exactly `rate.ticks capacity` ticks to the completed row. So the
  envelope-tick statement of B8 is instantiable without a measured count. The premise is
  inhabited (`nat7_envelope_inhabited`).
- `tariff_residual`: the success pin is public. A tariff below the worst case over the secret
  domain therefore distinguishes the secrets.

### The one-row trace leak (`Assurance/ObjectiveZkTraceDisclosure.lean`, compiled)

- One real row plus one hiding row makes every column `a + bX`. Opening at ζ, with 1 and ζ
  independent, determines both coefficients, and so the row (`one_row_opening_reveals`,
  `one_row_value_revealed`).
- The independence premise is satisfiable (`independence_satisfiable`) and refutable
  (`independence_needed`).
- Padding by repetition without masking makes every opening the row itself
  (`repeated_row_opening_is_row`), and the padded matrix is injective in the row
  (`padded_rows_determine_row`).

### Hypotheses that remain, by name

1. PCS verification ⇒ `BendTraceDirect.lower … Holds` (native soundness; Fiat–Shamir/QROM).
2. Link 5: the verifier's result wires are read by `ObjectiveDemandRegions.state layout`.
3. A universal `LayoutCodec`, one whose decoder is the layout decoder on every row, for a
   controller that dispatches every Core4 opcode (cv `01a1065a`). Today it is per run.
4. Transcript zero knowledge beyond the one-row and repetition facts (B9).
5. Collision resistance of the cSHAKE commitments. `ObjectiveProofContext.Collision` carries
   collisions constructively; there is no injectivity assumption.
