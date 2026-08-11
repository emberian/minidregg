# minidregg

**A Lean-first semantic kernel, heterogeneous proof fabric, and authenticated causal medium for
users and agents.**

**Project site:** [emberian.github.io/minidregg](https://emberian.github.io/minidregg/)
(source in [`website/`](website/) — deploys via GitHub Pages).

minidregg is building four things as one construction:

1. a **semantic kernel** for typed requests, request-indexed authority, canonical state
   transitions, flat multi-cell hyperedges, and receipts;
2. **Loom**, a proof-assurance layer that lets binary fields, prime fields, lookup/RAM, FHE rings,
   MPC shares, privacy proofs, and history keep honest native dialects while meeting at checked
   representation boundaries;
3. **Hyperdocuments**, a proof-native causal medium with typed content, stable ranges,
   transclusion, backlinks, annotations, offline branches, explicit conflicts, and versioned
   history; and
4. a **Lean-owned compiler and deployment boundary** in which generated artifacts describe
   native work, opaque native code returns bytes or an error, and only Lean can accept a turn.

The intended result is not merely a faster prover. A user should be able to inspect what changed,
who authorized it, which private or remote work was relied on, and which history made it current.
An agent should be able to follow typed links, compose bounded actions, work offline, publish a
joint turn atomically, and hand another agent a receipt instead of an unauditable assertion.

Lean is the sole source of semantic meaning, protocol control, and acceptance. Rust has no formal
operational semantics in this repository: it is mechanically generated data/dispatch glue or
opaque fallible computation. It is never described as a refinement and never supplies an
acceptance bit.

The stable architecture and construction order live in [`PROJECT.md`](PROJECT.md).
[`GOAL.md`](GOAL.md) is the current evidence ledger; older entries there are historical records,
not current deployment claims.

## Why Loom?

No one arithmetic field or execution model is honestly native to all of bits, sparse memory,
prime-field proofs, residue-ring FHE, MPC shares, privacy, and unbounded causal history. Forcing
them into one universal dialect hides conversions and usually moves the hardest security claims
into handwritten glue.

Loom owns the joints instead: roots-before-challenges control, explicit failure events and error
budgets, exact common-opening relations, proof-carrying history attribution, and Lean-owned
admission. Native dialects keep the work they do well. A verified semantic event is the narrow
waist through which their claims meet.

This choice is falsifiable. If a simpler formalizable stack supplies the same heterogeneous,
straight-line-knowledge, privacy, and history guarantees—or if Loom's shared joins do not remove
duplication and benchmark competitively—we should replace it. See
[`D-0004`](docs/decisions/D-0004-why-loom.md).

## Maturity legend

Every substantial claim is labeled by the strongest boundary actually closed:

| Level | Meaning | What it does **not** imply |
|---|---|---|
| **S — semantic/formal** | A Lean carrier, relation, theorem, reduction shape, or exact codec exists. | Executable online control or cryptographic security. |
| **A — admission/controller** | A Lean-owned controller consumes bounded bytes/errors and can construct the sole accepted result. | That the cryptographic premises have been reduced and priced. |
| **P — proof/security** | Concrete PCS/commitment/ROM/proximity/ZK assumptions and reductions are joined on the relevant game coin and error budget. | Deployment, persistence, or consumer cutover. |
| **D — deployment** | Authenticated artifacts, codecs, controllers, handlers, and storage are joined and used by a real consumer. | Competitive performance. |
| **B — benchmark** | Reproducible committed-source evidence measures the actual selected path against a stated workload. | Semantics, security, or a universal performance threshold. |

“Complete” without one of these boundaries is avoided.

## Current construction

| Pillar | Landed boundary | Honest residual | User/agent payoff |
|---|---|---|---|
| **Canonical semantic turn** | **S/A.** `AcceptedCellEffect` retains one exact authorization token, effects digest, and pre-root. `AcceptedCellEffectRequestBinding` adds a family-selected lawful argument projection and exact `argsDigest` equality without adding a second authority or interpreter. `CanonicalTransition` derives one post-state and delta. `DeclaredHyperedge` composes a flat, balanced multi-cell turn. | Digest reflection/CR is explicit. Physical CAS, WAL recovery, replication, liveness, and consumer migration require deployment refinements. | One inspectable reason for one state change; no hidden call-graph semantics. |
| **Durable settlement** | **S.** The durable model names root compare-and-swap, nullifiers, exact multi-cell charge, history append, idempotency, and crash outcomes. Successful settlement has a proved joint result. `ImplementationRefinement` now has an inhabitant: `Kernel.DurableWalHandler` is a staged/committed/compacting write-ahead log whose recovery fold tracks the model, and whose guard-less append is representable by no schedule at all. | That handler is a device MODEL — no fsync, torn record, byte codec, page cache, replication, clock, or liveness. A physical store must still exhibit ITS state as a `WalState` and ITS transitions as `WalStep`s, and owes codecs and tariff. No persistence or availability is inferred. | Retries cannot silently double-spend or split a joint turn when the handler implements the model — and the model is now known to be implementable at all. |
| **Hyperdocuments** | **S/A, and see the caveat — this row is currently VACUOUS at its cells.** Typed content, links/transclusions, stable ranges, marks/annotations, causal events, accepted content+event publication, exact-head history admission, and atomic two-cell publication exist as Lean carriers and theorems. Offline/concurrent merge preserves every current parent: singleton field sources write; 2+ sources become provenance-bearing `ConflictRecord`. An ancestry-backed accepted merge retains the selected-base realization/root; ambiguous/unavailable bases stay absent. `HyperdocumentInterface` adds versioned first-order query/action negotiation with lawful arguments and exact request-indexed authority. | **`Theory.MaterializerCardinality.hyperdocumentMaterializer_isEmpty` proves `Hyperdocument.Materializer Digest` is EMPTY**, because `LogicalState` is a total function over an infinite address space and a `LawfulCodec` cannot inject that into `List UInt8`. So every theorem above quantified over a document cell is vacuously true until `LogicalState` becomes finitely supported. Beyond that: no arbitrary unique-LCA claim, CRDT conflict policy, physical persistence/finality, authenticated history query resolver, complete editing grammar, search/GC, or migrated UI. PCS/CR/ROM remain premises at history admission. | Once the cells are inhabitable, users and agents can keep provenance, negotiate the same typed interface, publish linked changes together, branch offline, and see conflicts instead of losing a writer. |
| **Reactive/private computation** | **S/A.** Reactive promises fix their late-advice codec/carrier, wake only from a complete verified history entry, retain the observed pre-root, deadline, footprints, and replay nullifier, and finalize as an accepted effect/hyperedge incidence; physical release still needs external evidence. Private computation remains sealed. The note-spend path now has a bytes/error controller whose canonical statement is projected from that sole accepted core and whose roots precede its challenge. | Note-spend proof-suite ID is still `0`; PCS, CR, ROM, proof-of-knowledge, and hiding are distinct premise-shaped failure classes, not implementations. No confidentiality, malicious MPC, FHE soundness, durable reactive handler, or causal disclosure adapter is claimed. | An agent can resume authenticated work or request sealed computation without acquiring authority to reveal its output. |
| **Tower256 additive FRI** | **S/A with an exact conditional P reduction.** Lean defines exact Tower/Fan–Paar coordinates, cSHAKE framing, Merkle/controller schedule, coherent openings, folds, and final polynomial. Accepted bytes select the literal ideal challenge/query coin, the exact UD theorem supplies the additive event and price, and false acceptance is derived into additive-proximity or oracle-transport failure without a caller-supplied cover. | Exact cSHAKE/common-coin transport remains a premise. The raw non-binding carrier now exists on both the additive and history sides — `RawMerklePcs` and `RawHistoryBcsOpenings` retain the adversary's unequal accepted opening instead of erasing it, and `RawHistoryCollisionBridge` carries it to the landed framed cSHAKE collision at any alphabet size. That is a reduction with no price: no collision probability, no ROM realization, no deployed port identity. Executable reflected checker, deployed codecs/IDs, and matched E2E benchmark remain. | Binary-native work can be checked without pretending it is prime-field arithmetic. |
| **Tower256 lookup/LogUp** | **S/A.** Canonical Boolean addresses give exact unit-vector incidence and indexed evaluation. The extension-only clause-404 controller fixes one shared backend, issues first-order queries, accepts exactly two keyed native byte replies, and reconstructs the existing verified execution. Missing/duplicate/wrong-count replies block. | Clause 404 remains absent from base V1 and deployment. Position binding, PCS/sampled-decider soundness, CR/ROM, common-game history join, mutable RAM, artifact-native work profile, and deployed evidence remain. | Large sparse objects and authenticated indexes can be checked at the coordinates actually used. |
| **History and accumulation** | **S/A, conditional P shape.** The retained history now supplies the literal BCS/Fiat–Shamir verifier event rather than an external proxy; exact native-game pricing and common-coin transport are stated. That actual history event and the additive controller share one four-event game. | The same-coin `PcsCrRomReduction.classify` remains the concrete computational obligation, alongside common-coin transport, PCS, CR/binding, ROM, MCA/code-exact premises, hiding, and deployment. | A later light client can verify a long causal story from a small checkpoint while retaining exactly which semantic turns it represents. |
| **Ext6 gate proof** | **S/A.** `GateFactoredExt6` proves seven-operand provenance and the controller fixes the canonical statement/transcript. Eight local failure classes now inhabit a disjoint extensible global ledger on the same coin; the finite union bound includes base and Ext6 events without independence. | Real PCS, subfield proof, proximity, binding, ROM, challenge-sampling price, final LDT, recursion, and deployed 137-bit security remain. Ledger registration does not construct these reductions. | Prime-field application constraints can retain their own proof dialect and enter the same receipt boundary. |
| **Compiler and native authority** | **S/A/D for artifact/control identity, B for dispatch microbenchmark.** Base artifact work `9101` remains Tower256 dot product. The clause-406 deployment artifact additionally authenticates work `9102`, empty request codec `9003`, and 144-byte response codec `9005`; generated Rust returns candidate bytes and Lean decodes 36 canonical little-endian BabyBear words before descriptor certification. | Rust remains opaque and fallible. There is no Rust semantics, refinement, FFI proof, or cross-language correctness theorem. The generated zero witness is candidate compute, not a native verdict. | Native acceleration can be replaced or moved across hosts without changing semantic authority. |
| **Deployment registry** | **D for the narrow clause-406 byte path.** Clause 406 now has an authenticated artifact/native work/controller/deployment join; honest generated bytes certify, malformed bytes reject, and native errors block. | Base V1 itself still has zero clauses. Clause 404 remains gated/absent. BFV 901 remains reserved. Clause 406 proves only the exact BabyBear add-1 zero-witness descriptor path, not a deployed proof system or Rust correctness. | A user or agent can distinguish one actually available checked byte path from gated or reserved catalog entries. |

### The cells are not yet inhabitable

`Theory.MaterializerCardinality` and `Kernel.EventLogMaterializerLimit` prove that **all
four** `CellState.Schema` definitions in this repository admit **no materializer**:
credential authority, Hyperdocument content, the Hyperdocument event log, and the legacy
turn effect schema that `Kernel.DeclaredHyperedge` uses. A materializer carries a
`LawfulCodec` for the schema's entire `LogicalState`, which is a total function over an
infinite field index; no encoding injects that into `List UInt8`. Every theorem quantified over a
`Materialized` cell at a deployed schema is therefore vacuously true — credential
issuance, attenuation, revocation, epoch rotation, the whole Hyperdocument operations
layer, the atomic two-cell publication, and the flat multi-incidence turn.

Nothing proved is false, and the schemas themselves are not the problem. It is one
type-level decision applied uniformly, and
`materializer_nonempty_iff_countable` states exactly what replacing it must achieve.

The fix is the vocabulary these modules already use about themselves: make `LogicalState`
finitely supported — a finite map read through a default — and the state space is
countable whenever index and values are. It has not been done.

### Carriers, exhibited

A theorem quantified over an empty type is true and worthless. As of 2026-08-10 the
load-bearing carriers are exhibited at built parameters rather than assumed inhabitable:
`CellState.ValidatedPatch`, `TypedAuthorization.Authorized`, `AcceptedCellEffect`,
`CanonicalTransition.PreparedTurn` (with a post-root that actually moves),
`SemanticHistoryFamily.VerifiedHistoryHead` (with a real fold round),
`TypedCellHyperedge.Commit`, and `MultiCellHyperedge.Commit` (two incidences over two
different schemas, balancing by cancellation). Each witness ships with refutations
showing its equations are constraints.

Every one of those uses BUILT parameters — a minimal schema, a permissive portal — so
none of them says anything about the deployed ones, and a permissive portal is exactly
the portal a security claim may not use. `HyperdocumentAgentOperation.AcceptedOperation`
is the largest carrier still unexhibited.

This is a frontier research stack, not a production prover.

## What runs today

There is deliberately no authoritative Rust one-call prover/verifier API. The former
BabyBear⁴/FRI/WGPU and reference prover/verifier paths were deleted because they duplicated
transcript and acceptance semantics. Current native source is limited to fallible arithmetic,
transform, hash, and MLE/lookup candidate compute plus generated artifact/dispatch data.

The generated [`semantic_artifact_v1.rs`](prover/generated/semantic_artifact_v1.rs) is derived
from the base authenticated Lean artifact and exposes Tower256 dot-product work `9101`. The
clause-406 deployment extends that artifact with generated
[`semantic_artifact_arithmetic.rs`](prover/src/semantic_artifact_arithmetic.rs), work `9102`, and
its exact byte codecs. Rust returns 144 candidate bytes; Lean alone decodes, checks the emitted
descriptor, and constructs the certificate.

Five concrete controller seams now exist:

- **Arithmetic clause 406:** a deployed byte-backed controller/artifact/native-work loop whose
  opaque Rust candidate is decoded and accepted only by Lean;
- **Tower256 additive FRI:** complete deterministic control through openings, folds, and terminal
  polynomial, with security reductions still explicit;
- **extension-only lookup clause 404:** exact two-reply byte dispatch into the existing verified
  LogUp execution, still excluded from deployment; and
- **Ext6 gate proof:** exact deterministic transcript/algebra control, with its PCS and security
  game obligations still open; and
- **sealed note spend:** canonical statement and bytes/error controller control exist; proof suite
  `0` and the cryptographic/hiding laws remain explicit premises.

Native failure can block availability. It cannot create an accepted receipt.

## A compound-document analogy, not a lineage claim

DCOM/OLE and related compound-document systems had a useful instinct: documents could be active,
embedded, linked, remotely activated, and negotiated through interfaces. minidregg does not claim
direct lineage or a one-for-one replacement. It studies what those ideas look like after removing
ambient pointers, hidden mutation, location/configuration authority, and runtime object identity.

| Earlier systems idea | minidregg design contrast |
|---|---|
| monikers | stable typed content-addressed references |
| structured storage | canonical sparse authenticated cells |
| embed/link | authenticated transclusion, backlinks, and causal history evidence |
| `QueryInterface` | explicit typed effect family and manifest clause; no runtime object authority |
| marshaling / proxy-stub | lawful codecs and generated bytes/error dispatch |
| COM aggregation | one flat typed multi-cell hyperedge |
| connection points | verified reactive lifecycle |
| DTC-style commit | fail-closed multi-root/nullifier/budget/history journal model |

The common design question is how active compound media can compose. The changed answer is that
identity, authority, state transition, and history must be explicit evidence rather than ambient
runtime convention.

## Consumers and subsumption gate

minidregg is not a replacement kernel merely because its model is elegant. Subsumption requires a
real adapter and cutover for each consumer:

| Consumer family | Required proof of replacement | Intended outcome |
|---|---|---|
| Drex/FHEgg/Dark Bazaar | private compute request, ring proof, resource effects, settlement, and separately authorized release | Delegated sealed computation and trade without delegating disclosure. |
| DeOS / agent platform | reactive projections, dependency invalidation, promises, tools, intent/completion receipts | Agents act through bounded capabilities and resumable audited workflows. |
| token authorization | typed request, current authority/revocation/nullifier state, canonical accepted effect | A token explains exactly one permitted transition. |
| Grains | causal receipt chain and succinct checkpoint with exact retained semantics | Portable verifiable history rather than trusted replay. |
| DreggNet cloud/control plane | multi-resource command, durable settlement handler, external completion evidence | Retriable orchestration without confusing intent, admission, and physical completion. |
| hypermedia clients | stable ranges, transclusion/backlinks, branch/merge/conflicts, current-authority settlement | A shared medium users and agents can inspect, annotate, and extend offline. |

No row is “subsumed” before **D** evidence, and no performance claim is accepted before a matched
**B** workload.

## Performance evidence

The current dispatch benchmark measures only the generated catalog/dispatch overhead around work
`9101`, not proof-system throughput. At source commit `54295c6` with evidence commit `4d1f290`,
direct and generated-dispatch results were byte-identical. Across vector lengths 1–16384, measured
dispatch/direct ratios were approximately `0.985–1.040` on hbox and `0.985–1.025` on persvati.
This is empirical noise-scale evidence for this work profile, with no claimed threshold and no
semantic implication. See [`docs/PERFORMANCE.md`](docs/PERFORMANCE.md).

The performance thesis is locality-aware: dense and sparse equality representations, checkpoint
cadence, proof size, memory traffic, tail latency, and CPU/SIMD/GPU crossover must be measured on
the actual admitted protocol. Historical deleted-prover measurements remain archived only as
historical evidence.

## Trust and claim discipline

- Standard Lean axioms reported by `#print axioms` are not hidden as implementation evidence.
- An imported mathematical theorem interface is labeled conditional until its proof is local or
  mechanically linked.
- A controller theorem is not a cryptographic reduction.
- A registry pin is not an implementation.
- A generated artifact is not a proof of native behavior.
- Conformance tests are not semantics.
- A modeled durable transaction is not a persisted transaction until a handler refinement exists.
- A historical result from a deleted path is not current runtime evidence.

## Repository map

- [`Theory/`](Theory/) — semantic state, requests, authority, effects, hyperdocuments, codecs, and
  native mathematical dialects;
- [`Kernel/`](Kernel/) — categorical foundations, canonical transitions, hyperedges, merges, and
  durable settlement models;
- [`Loom/`](Loom/) — codes, proximity, accumulation, games, extraction, and ZK;
- [`Compiler/`](Compiler/) — derived AIR, emit/artifact generation, controller plans, manifests,
  dispatch, and deployment joins;
- [`Assurance/`](Assurance/) — security budgets, admission, history, common-game statements, and
  cross-layer theorem joins;
- [`prover/`](prover/) — opaque native candidate compute, generated data/dispatch, tests, and
  benchmarks;
- [`docs/decisions/`](docs/decisions/) — architectural decisions and claim ceilings.

## Build and reading order

```bash
lake build
cd prover && cargo test
```

Start with [`PROJECT.md`](PROJECT.md), then
[`docs/decisions/D-0002-canonical-hyperedge-kernel.md`](docs/decisions/D-0002-canonical-hyperedge-kernel.md),
[`docs/decisions/D-0005-hyperdocument-semantic-family.md`](docs/decisions/D-0005-hyperdocument-semantic-family.md),
[`docs/PROVER-PLAN.md`](docs/PROVER-PLAN.md), and
[`docs/LOOM-COMPLETE.md`](docs/LOOM-COMPLETE.md). Use [`GOAL.md`](GOAL.md) for evidence and history,
not as a substitute for the current claim ceilings above.
