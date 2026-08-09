# minidregg

**A Lean-first semantic kernel, heterogeneous proof fabric, and authenticated causal medium for
users and agents.**

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
| **Durable settlement** | **S.** The durable model names root compare-and-swap, nullifiers, exact multi-cell charge, history append, idempotency, and crash outcomes. Successful settlement has a proved joint result. | A deployment must instantiate `ImplementationRefinement` for its bytes, transactions, WAL/recovery, replication/failover, codecs, and tariff. No persistence or availability is inferred from the model. | Retries cannot silently double-spend or split a joint turn when the handler implements the model. |
| **Hyperdocuments** | **S/A.** Typed content, links/transclusions, stable ranges, marks/annotations, causal events, accepted content+event publication, exact-head history admission, and atomic two-cell publication exist. Offline/concurrent merge preserves every current parent: singleton field sources write; 2+ sources become provenance-bearing `ConflictRecord`. Proven ancestry selects a base only when justified. | No arbitrary unique-LCA claim, CRDT conflict policy, physical persistence/finality, complete editing grammar, search/GC, or migrated UI. PCS/CR/ROM remain premises at history admission. | Users and agents can keep provenance, publish linked changes together, branch offline, and see conflicts instead of losing a writer. |
| **Reactive/private computation** | **S/A.** Reactive control is joined to canonical patches. Private computation's authoritative `CoreRequest` contains program/relation, input identities and bridge, output commitment, resource effects, footprint, nullifier, and mode pins—no disclosure policy masquerading as computation. Accepted computation is forced sealed and retains no release value. BFV binds all 384 exact equations. | No confidentiality, ZK, MPC malicious security, FHE soundness, deployed BFV codecs/controller, or causal disclosure adapter is claimed. Release is a later separately authorized effect. | An agent can request sealed work without acquiring authority to reveal its output; a user can audit computation and disclosure as separate events. |
| **Tower256 additive FRI** | **S/A.** Lean defines exact Tower/Fan–Paar coordinates and 32-byte codec, cSHAKE256 framing, Merkle scheme, transcript schedule, coherent openings, folds, and final polynomial. The controller accepts arbitrary native bytes/error only after Lean decoding and checks, and reaches the exact ideal clause on one game coin. | The same-coin false-accept cover into proximity/binding/oracle events, concrete CR price, cSHAKE→ROM transport, far-word FS reduction, executable reflected checker, deployed codecs/IDs, and matched end-to-end benchmark remain. | Binary-native work can be checked without pretending it is prime-field arithmetic. |
| **Tower256 lookup/LogUp** | **S/A.** Canonical Boolean addresses give exact unit-vector incidence and indexed evaluation. The extension-only clause-404 controller fixes one shared backend, issues first-order queries, accepts exactly two keyed native byte replies, and reconstructs the existing verified execution. Missing/duplicate/wrong-count replies block. | Clause 404 remains absent from base V1 and deployment. Position binding, PCS/sampled-decider soundness, CR/ROM, common-game history join, mutable RAM, artifact-native work profile, and deployed evidence remain. | Large sparse objects and authenticated indexes can be checked at the coordinates actually used. |
| **History and accumulation** | **S/A, conditional P shape.** Loom has exact folding, depth composition, extraction, retained semantic history, unshifted BCS reconstruction, and a history game that keeps PCS/binding/ROM premises on one coin. Exact-head finality and finite multi-field post layout are indexed in Lean. | Concrete PCS, commitment CR/binding, ROM transport, MCA/error hypotheses, hiding/sub-UD, and the end-to-end additive/history common-cover theorem remain. The pending checkpoint join is not counted until committed. | A later light client can verify a long causal story from a small checkpoint while retaining exactly which semantic turns it represents. |
| **Ext6 gate proof** | **S/A.** `GateFactoredExt6` proves seven-operand provenance, degree-two rounds, terminal affine forms, and eta aggregation. The Lean controller fixes descriptor bytes, receipt codecs, cSHAKE challenges, transcript order, and the full algebraic verifier relation over arbitrary native bytes/error. Admission names seven failure events on one finite coin. | Real PCS, base-subfield proof, proximity, binding, ROM transport, final LDT, global ledger injection, recursion, and deployed 137-bit security remain. | Prime-field application constraints can retain their own proof dialect and enter the same receipt boundary. |
| **Compiler and native authority** | **S/A/D for artifact identity, B for dispatch microbenchmark.** Canonical artifact encoding/content address/JSON authenticates the manifest, ABI codecs, and native work catalog. Exactly one current native work profile, Tower256 dot product `9101`, is generated into Rust with request codec `9001` and response codec `21`. Generated dispatch and direct execution return byte-identical results in the recorded benchmark. | Rust remains opaque and fallible. There is no Rust semantics, refinement, FFI proof, or cross-language correctness theorem. Artifact closure authenticates declared transport/control data, not native computation. | Native acceleration can be replaced or moved across hosts without changing semantic authority. |
| **Deployment registry** | **A/D boundary.** `ComposableDeploymentManifest` admits clauses only from real controller entries and joins artifact, manifest, controller-registry, and native-catalog well-formedness. Clause 406 has a deterministic Lean controller. Security-gated and reserved clauses cannot project into deployment. | Base V1 has zero dialect clauses. Clause 404 is gated, not deployed. BFV 901 is reserved with zero proof-suite/controller pins. Clause 406 has no emitted Rust byte profile. | A user or agent cannot mistake a catalog entry or marketing label for an available verifier. |

This is a frontier research stack, not a production prover.

## What runs today

There is deliberately no authoritative Rust one-call prover/verifier API. The former
BabyBear⁴/FRI/WGPU and reference prover/verifier paths were deleted because they duplicated
transcript and acceptance semantics. Current native source is limited to fallible arithmetic,
transform, hash, and MLE/lookup candidate compute plus generated artifact/dispatch data.

The generated [`semantic_artifact_v1.rs`](prover/generated/semantic_artifact_v1.rs) is derived
from the authenticated Lean artifact. Its native catalog currently exposes Tower256 dot product
work `9101`; the generated dispatcher validates catalog-selected identifiers and codecs before
calling opaque Rust and returning bytes/error. Lean still owns decoding, transcript control,
proof checking, and acceptance.

Three concrete controller seams now exist:

- **Arithmetic clause 406:** a deterministic descriptor controller and honest non-vacuity tooth;
- **Tower256 additive FRI:** complete deterministic control through openings, folds, and terminal
  polynomial, with security reductions still explicit;
- **extension-only lookup clause 404:** exact two-reply byte dispatch into the existing verified
  LogUp execution, still excluded from deployment; and
- **Ext6 gate proof:** exact deterministic transcript/algebra control, with its PCS and security
  game obligations still open.

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
