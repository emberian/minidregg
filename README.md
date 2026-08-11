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
| **Canonical semantic turn** | **S/A.** `AcceptedCellEffect` retains one exact authorization token, effects digest, and pre-root. Policy address and membership are committed by authority state. `CanonicalTransition` derives one post-state and delta. Canonical resource operations derive the installed patch, the typed/multi-cell conservation law, and an exact authorized ten-lane charge; an executable two-leg `DeclaredHyperedge` crosses the exact typed-cell bridge. | Digest reflection/CR is explicit. The old single-turn/integer-resource carriers remain compatibility surfaces. Physical transaction, storage, liveness, and consumer migration require deployment refinements. | One inspectable reason and tariff for one state change; no hidden call-graph semantics or caller-invented balance. |
| **Durable settlement** | **S/A-model, exercised local slice.** Payload-bearing `DataIntent`s retain canonical bytes, guards, nullifiers, charges, events, and replay identity. Fee-first admission, reactive terminal/outbox settlement, versioned/checksummed WAL frames, torn-tail repair, and quorum safety have concrete witnesses. The bounded link store additionally exercises stage/crash, separate-process restart, exact retry, and conflict/no-overwrite behavior. | `DeviceStep.sync` and the local Rust store are explicit models/adapters, not proofs of POSIX/fsync, stable media, power-loss behavior, hostile races, authenticated voting, or replication liveness. | The selected link slice can be restarted and retried without semantic duplication; broader physical guarantees remain explicit. |
| **Hyperdocuments** | **S/A plus a bounded D-shaped slice.** Accepted link/event posts are welded to exact bounded page deltas, framed bytes, cSHAKE roots, and an authority guard. Human and agent use the same command bytes; local restart/retry reopens the exact link. Authorized content/history queries, typed transclusion reopening, a persistent bounded backlink/range index, schema migration, and two-parent conflict preservation are concrete. | No production editor/runtime deployment, signature/key custody, global crawler completeness, POSIX proof, authenticated network finality, PCS/CR/ROM security, or end-to-end service SLO is claimed. | One typed forward link now crosses semantic acceptance, bounded representation, local restart, retry, and exact query; offline conflicts and bounded references remain inspectable. |
| **Bounded deployment pages** | **A/B (narrow).** Versioned four-slot content, event-history, authority, and backlink-index pages have lawful exact codecs, sparse projections, Lean cSHAKE roots, catalog pins, routing, V1→V2 migration, and dual-host interpreter evidence. Exact accepted link/event records now produce their page deltas and durable bytes. | The four older full-cell registry codecs remain inhabitation-only. Pairwise digest binding, real transactional I/O, concurrency, memory/tail latency, and native runtime refinement remain separate. | Compact formats can be named, migrated, recovered, queried, and measured instead of inferred from existence codecs. |
| **Escrow and provider settlement** | **S/A-model with concrete consumers.** Public orders settle deposit/fill/cancel/expiry/refund; an inhabited sealed shared-MPC result enters escrow while declassification remains a separate authorization. A DreggNet witness binds market fill to a prepaid provider lease, idempotent invocation, terminal/outbox, refund, replay, and quorum uniqueness. | Provider correctness, oracle evidence, private channels, OS/cloud execution, authenticated votes, network liveness, and production client cutover remain premises. | Agent-market and cloud-job flows now share exact economic and terminal laws without granting semantic authority to the external worker. |
| **Reactive/private computation** | **S/A.** A leased Hyperdocument link job now reaches authenticated notification, reaction, finalization, dependency invalidation, and atomic terminal/outbox replay. Shared MPC has an inhabited sealed accepted cell and private-escrow join; BFV has a concrete all-384-row checked batch/cell. NoteSpend and BFV still distinguish reflected control from semantic proof admission. | Current proof-suite pins remain zero/non-deployable; arithmetic/PCS/CR/ROM/PoK laws, hiding, executor conformance, scheduler fairness, delivery ACKs, and confidentiality remain separate. | Agents can resume authenticated jobs and request sealed computation without receiving an implicit release capability. |
| **Tower256 additive FRI** | **S/A with an exact conditional P reduction.** Concrete raw PCS levels, statement codecs, an opaque-byte verifier witness, and an actual receipt-derived execution game now retain collision or transcript-mismatch events. Accepted bytes select the literal ideal challenge/query coin, and the exact UD theorem prices additive proximity. | The nontrivial demo statement and closed verifier witness are still separate bootstrap shapes. Concrete far-statement execution, cSHAKE/common-coin transport, collision/ROM prices, native endpoint, and end-to-end benchmark remain. Universal `PositionBinding` is formally impossible at positive height and is not a residual to “fill.” | Binary-native work can be checked without pretending it is prime-field arithmetic or hiding equivocation behind an impossible premise. |
| **Tower256 lookup/LogUp** | **S/A with extension identity.** Canonical Boolean addresses give exact unit-vector incidence and indexed evaluation. Clause 404 now has nonzero/versioned extension controller/work/codec pins, concrete shared-backend `ControllerInputs`, exactly two challenge-indexed byte calls, and a non-vacuous honest verified reflection; malformed/missing/duplicate/wrong-slot/native-error replies block. | Clause 404 remains absent from base V1. Admission still requires explicit table/checkpoint binding, PCS/sampled-decider, CR/ROM, same-coin history/oracle evidence, and mutable-RAM consistency; controller inhabitation does not prove or price them. | Large sparse objects and authenticated indexes can be checked at the coordinates actually used without silently promoting an extension into base deployment. |
| **History and accumulation** | **S/A with an intrinsic native-FS price.** Raw verifier-owned bytes now equal the literal SR trace/output/final challenge and project exact messages, roots, columns, and checkpoint tape. The Def-B.2 false-accept event constructs the intrinsic PCS/MCA classifier, and exact FS soundness transports its native price on the common coin. | The SR coin omits the complete fresh cSHAKE query table, so no honest Merkle birthday/ROM term is yet derivable. Hiding, deployed PCS, availability, and network finality remain open; the old binding-closed `JointGameFamily` stays retired. | History no longer needs an arbitrary classifier or erased equivocation to state its actual failure event. |
| **Ext6 gate proof** | **S/A.** `GateFactoredExt6` proves seven-operand provenance; nonzero suite/controller identity, four codec pins, a concrete 23-residual/5-round statement, and reflected opaque-byte control now inhabit the deployment carrier. Eight disjoint same-coin failure classes remain the semantic admission boundary. | No positive secure proof follows from control alone: the maximal residual is formally total. Real PCS, subfield proof, proximity, binding, ROM, challenge-sampling price, final LDT, recursion, and deployed 137-bit security remain. | Prime-field constraints can retain their own proof dialect and exact controller identity without a false security claim. |
| **Compiler and native authority** | **S/A/D for artifact/control identity, B for dispatch microbenchmark.** Base artifact work `9101` remains Tower256 dot product. The clause-406 deployment artifact additionally authenticates work `9102`, empty request codec `9003`, and 144-byte response codec `9005`; generated Rust returns candidate bytes and Lean decodes 36 canonical little-endian BabyBear words before descriptor certification. | Rust remains opaque and fallible. There is no Rust semantics, refinement, FFI proof, or cross-language correctness theorem. The generated zero witness is candidate compute, not a native verdict. | Native acceleration can be replaced or moved across hosts without changing semantic authority. |
| **Deployment registry** | **D for the narrow clause-406 byte path.** Clause 406 now has an authenticated artifact/native work/controller/deployment join; honest generated bytes certify, malformed bytes reject, and native errors block. | Base V1 itself still has zero clauses. Clause 404 remains gated/absent. BFV 901 remains reserved. Clause 406 proves only the exact BabyBear add-1 zero-witness descriptor path, not a deployed proof system or Rust correctness. | A user or agent can distinguish one actually available checked byte path from gated or reserved catalog entries. |

### The sparse-cell obstruction is closed

The former `LogicalState.fields` was a total dependent function.  Over each deployed
infinite address space it contained an uncountable function space, so no `LawfulCodec`
and therefore no `Materializer` could exist.  `Theory.MaterializerCardinality` retains
that argument against the deleted carrier as a regression tooth.

`CellState.FieldStore` is now one canonical dependent finite map.  Primitive reads return
`Option`; semantic defaults such as zero epochs and false revocation membership are
explicit reader policies.  Typed patches assign `some value` or structural `none`, so
deletion does not require an application tombstone.  Declared turns keep their total
semantic evaluator but reify
only the exact finite footprint over a canonical pre-state, with a proved outside-frame
law.  Authority, Hyperdocument content, and the append-only event log use the same sparse
carrier directly.

`Theory.DeployedMaterializerWitness` exhibits codecs, materializers, and cells for the
declared-effect, authority, and Hyperdocument schemas.  `Kernel.DeployedMaterializerWitness`
does the same for the event log and proves its sparse-RAM and canonical-cell empty roots
are exact.  Those four countability-selected full-cell codecs close vacuity only.  The
finite-sparse audit distinguishes them from three concrete pinned bounded-page codecs.
For the forward-link slice, accepted content and event posts now refine to exact page
deltas, bytes, cSHAKE roots, and an authority-guarded durable intent; general accepted
posts, pairwise digest binding, and physical storage remain deployment obligations.

### Carriers, exhibited

A theorem quantified over an empty type is true and worthless. As of 2026-08-10 the
load-bearing carriers are exhibited at built parameters rather than assumed inhabitable:
`CellState.ValidatedPatch`, `TypedAuthorization.Authorized`, `AcceptedCellEffect`,
`CanonicalTransition.PreparedTurn` (with a post-root that actually moves),
`SemanticHistoryFamily.VerifiedHistoryHead` (with a real fold round),
`TypedCellHyperedge.Commit`, `MultiCellHyperedge.Commit` (two incidences over two
different schemas, balancing by cancellation), the deployed schema materializers,
the Hyperdocument causal family, canonical resource effects, and a committed two-leg
declared hyperedge whose typed post agrees with its legacy executable post. Each witness
ships with refutations showing its equations are constraints.

Every one of those uses BUILT parameters — sometimes a minimal schema or permissive
portal — so none alone says anything about physical deployment. Canonical policy
selection now binds an authority-state address and membership proof, and the bounded
link/credential consumers exercise restart and retry, but signature soundness, key
custody, physical-device refinement, and global availability are still obligations.
The largest remaining gaps are complete cSHAKE query-trace coupling and concrete
PCS/CR/ROM prices, nonzero production proof suites, authenticated network finality and
liveness, general page/storage refinement, and end-to-end client/service benchmarks.

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
- **extension-only lookup clause 404:** nonzero extension pins and exact two-reply byte dispatch
  into the existing verified LogUp execution, still absent from base V1;
- **Ext6 gate proof:** nonzero deployment-carrier identity and exact deterministic
  transcript/algebra control, with its PCS and security game obligations still open; and
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
- A modeled durable transaction—even with framed bytes, crash recovery, and quorum safety—is not
  a persisted transaction until an actual filesystem/database/network implementation refines it.
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
