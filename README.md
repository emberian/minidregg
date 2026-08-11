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
| **Durable settlement** | **S/A-model.** Payload-bearing `DataIntent`s retain canonical post bytes, read guards, nullifiers, charges, events, and replay identity. Fee-first admission, current-authority guards, reactive terminal/outbox settlement, and provider leases have concrete witnesses. Versioned/checksummed WAL frames model torn tails, crash repair, and exact recovery; intersecting-quorum certificates prove finality safety and failover replay. | `DeviceStep.sync`, quorum votes, and network delivery are Lean models—not POSIX/fsync/disk/Raft implementations. No actual filesystem/database refinement, authenticated voting, replication liveness, availability, or consumer D is inferred. | A conforming implementation cannot split a joint update, replay a charge, race stale authority, or finalize two different values in one slot. |
| **Hyperdocuments** | **S/A.** Alongside typed content, causal events, stable ranges and interface negotiation, there is now an accepted genesis→forward-link publication and exact history/query reopen. One byte endpoint shared by human and agent origins proves publish, lost-response crash, recovery, retry, and exact response decode. A concrete base→two-sibling merge retains both values in a provenance-bearing `ConflictRecord`; that conflict survives atomic publication, history opening, torn-tail recovery, retry, and quorum-finality safety. | These are proof-relevant witnesses and an admitted endpoint, not a migrated editor. Real credentials, physical storage/network refinement, authenticated finality, PCS/CR/ROM prices, search/GC, complete backlink indexing, and a client that actually calls the endpoint remain open. | The semantic/admission path needed for humans and agents to share links and preserve offline conflicts is concrete; the production application path is not yet cut over. |
| **Bounded deployment pages** | **A/B (narrow).** Versioned four-slot content, event-history, and policy/revocation pages have lawful exact codecs, canonical sparse projections, Lean cSHAKE roots, stable extension-catalog pins, cross-page link routing, and exact dual-host interpreter evidence. | Full semantic-cell post → exact page-delta refinement, real I/O, concurrency, CR, memory/tail latency, and native runtime evidence remain. The benchmark covers finite 1–4-slot Lean values only. | A deployment can name compact page formats and measure their actual Lean encoding/root/reopen path instead of relying on existence codecs. |
| **Escrow and provider settlement** | **S/A-model.** Canonical public orders authorize escrow deposit, partial/full fill, cancellation/expiry and residual refund; release, payment, fee, nullifier, exact ten-lane charge and order state settle together. Provider leases separately cover start/refuse/compensate/quarantine and terminal/outbox races. | Private-proof realization, price/oracle/provider evidence, native codecs, physical execution, refund transport, and market/client cutover remain explicit boundaries. | A future agent marketplace can reuse one exact order/lease settlement law without treating an external worker or oracle as semantic authority. |
| **Reactive/private computation** | **S/A.** A concrete Hyperdocument create event now inhabits host observation, proof data, controller layout, accepted transition, verified-history wakeup, and atomic terminal+outbox settlement; alternative terminals conflict and retries replay. Private computation remains sealed. Note spend and BFV distinguish weak reflected receipts from semantic admission, and a concrete note-spend computation adapter reaches one sealed accepted cell. | Current note/BFV statements are zero-pinned and formally non-deployable. Semantic admission still requires nonzero suite identity plus arithmetic/PCS/CR/ROM/PoK laws; hiding is separate. No scheduler fairness, delivery, confidentiality, malicious MPC, FHE security, or release adapter is claimed. | Agents can be modeled as resuming authenticated work or requesting sealed computation without gaining disclosure authority. |
| **Tower256 additive FRI** | **S/A with an exact conditional P reduction.** Concrete raw PCS levels, statement codecs, an opaque-byte verifier witness, and an actual receipt-derived execution game now retain collision or transcript-mismatch events. Accepted bytes select the literal ideal challenge/query coin, and the exact UD theorem prices additive proximity. | The nontrivial demo statement and closed verifier witness are still separate bootstrap shapes. Concrete far-statement execution, cSHAKE/common-coin transport, collision/ROM prices, native endpoint, and end-to-end benchmark remain. Universal `PositionBinding` is formally impossible at positive height and is not a residual to “fill.” | Binary-native work can be checked without pretending it is prime-field arithmetic or hiding equivocation behind an impossible premise. |
| **Tower256 lookup/LogUp** | **S/A with extension identity.** Canonical Boolean addresses give exact unit-vector incidence and indexed evaluation. Clause 404 now has nonzero/versioned extension controller/work/codec pins, concrete shared-backend `ControllerInputs`, exactly two challenge-indexed byte calls, and a non-vacuous honest verified reflection; malformed/missing/duplicate/wrong-slot/native-error replies block. | Clause 404 remains absent from base V1. Admission still requires explicit table/checkpoint binding, PCS/sampled-decider, CR/ROM, same-coin history/oracle evidence, and mutable-RAM consistency; controller inhabitation does not prove or price them. | Large sparse objects and authenticated indexes can be checked at the coordinates actually used without silently promoting an extension into base deployment. |
| **History and accumulation** | **S/A, conditional P shape.** The retained history supplies the literal BCS/Fiat–Shamir event. Raw openings and actual additive execution now join history PCS/MCA, additive proximity, extracted collisions, and literal transcript transport on one nonempty coin; scoped projections preserve exact roots over finite declared footprints. | The production raw Fiat–Shamir byte runner/extractor bridge, intrinsic MCA theorem, collision/ROM prices, hiding, and deployment remain. The old binding-closed `JointGameFamily` is formally impossible and retired. | A later light client can verify a causal story without erasing equivocation before it is priced. |
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
are exact.  Those countability-selected full-cell codecs close vacuity only.  Bounded
content/event/authority pages now add versioned concrete codecs, cSHAKE roots, and catalog
pins, but production still owes the exact refinement from every accepted semantic post to
those page deltas plus physical storage and cryptographic binding.

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

Every one of those uses BUILT parameters — a minimal schema, a permissive portal — so
none of them alone says anything about physical deployment. Canonical policy selection
now binds an authority-state address and membership proof, but physical registry
authentication and cryptographic binding are still deployment obligations. The largest
remaining gaps are the raw history Fiat--Shamir execution/security bridge, concrete proof
prices and suites, exact semantic-post-to-page refinement, and a real user/agent consumer
cutover over physical storage.

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
