# The minidregg project

This document is the stable construction plan. [`README.md`](README.md) explains the design point;
[`GOAL.md`](GOAL.md) records evidence and history.

## One sentence

Build a Lean-owned semantic computer in which users and agents can authorize, execute, inspect,
link, merge, and compress heterogeneous state transitions without giving native code, runtime
objects, or storage handlers a second source of meaning.

## Outcome first

The finished system should let a user ask:

- What exactly changed, from which root to which root?
- Which request, authority, resource law, private computation, and external completion justified it?
- Which causal parents and transcluded sources made this document current?
- Is a conflict explicit, or was one writer silently lost?
- Can I hand a compact proof of this history to another device or agent?

It should let an agent:

- follow typed content-addressed links and backlinks;
- inspect only authenticated coordinates of large objects;
- plan several effects and publish them as one balanced hyperedge;
- work on offline branches and merge without erasing provenance;
- invoke sealed computation without receiving disclosure authority;
- resume reactive work and external tools from explicit receipts; and
- replace a native accelerator without changing the semantic protocol.

## Maturity boundaries

Every pillar advances independently through five levels:

| Level | Closure |
|---|---|
| **S** | semantic/formal carrier and theorem |
| **A** | Lean-owned admission/controller over bytes/error |
| **P** | concrete cryptographic reductions and error game |
| **D** | artifact, handler, storage, and consumer deployment |
| **B** | reproducible matched-workload benchmark |

An **S** theorem cannot be advertised as **D**. An **A** controller cannot be advertised as **P**.
No consumer is replaced before **D**, and no performance conclusion is accepted before **B**.

## Target composition

```text
typed request + current authority + canonical pre-state
                         |
                         v
              Lean-owned effect family
                         |
                         v
        accepted effect + exact validated patch
                         |
                         v
       flat balanced multi-cell semantic hyperedge
                         |
             +-----------+-----------+
             |                       |
             v                       v
     durable settlement       causal receipt/history
             |                       |
             v                       v
       physical handler       Loom proof/checkpoint
                                     |
                        +------------+------------+
                        |            |            |
                     lookup      private/FHE    hypermedia
```

The narrow waist is one canonical semantic event:

- native statement;
- canonical representation/opening relation;
- one exact typed receipt clause; and
- one shared transcript and failure ledger when security is claimed.

Different dialects may represent work differently. They do not get parallel mutable state or
parallel authorization semantics.

## Hard invariants

### Semantic authority

1. Lean owns state meaning, request meaning, protocol control, and acceptance.
2. Rust has no semantics or refinement theorem in this repository.
3. Native work returns bytes or an opaque error; failure may block availability, never authorize.
4. Generated artifacts contain first-order data and dispatch identity, not verdicts.

### State and authority

5. One typed request names subject, target, verb, arguments, effects, policy, nonce, and exact
   pre-root.
6. `AcceptedCellEffectRequestBinding` completes common binding with a lawful family-selected
   argument projection; digest reflection/CR remains an explicit premise.
7. A validated patch derives one canonical post-state and exact footprint.
8. A multi-resource action is a flat finite hyperedge with one shared apex and aggregate law—not a
   hidden call forest.
9. Rejection has no post-state unless explicitly modeled as a charged committed effect.

### Privacy and external effects

10. Computation and disclosure are different effect families.
11. Private computation is sealed by default; a later release needs new authority and a causal link
    to an output commitment.
12. An intent/admission receipt is not proof that external I/O happened; completion/refusal is a
    later event.

### History and storage

13. A receipt binds exact pre/post roots, effect footprint, authority, native proof clauses, and
    predecessor evidence.
14. Causal history retains entry identity and occurrence; height alone is not finality.
15. Durable commit models root CAS, nullifiers, charges, history, idempotency, and crash outcomes,
    but deployment must refine actual transaction/WAL/replication behavior.

### Security and evidence

16. Roots precede challenges; representations meet through checked opening relations.
17. Every failure term names its event, coin space, and bound.
18. PCS, CR/binding, ROM transport, proximity, ZK, MPC, and FHE security are never inferred from a
    manifest pin or native kernel.
19. Remote and benchmark evidence identifies exact committed source and supports only its stated
    claim ceiling.

## Semantic machine

The semantic kernel is deliberately smaller than an application runtime.

### Canonical effects

`Theory.AcceptedCellEffect` retains the common authorization token, effect digest, pre-root,
validated patch, exact footprint, and family-specific evidence. The landed generic binding layer
adds exact `argsDigest` equality using a lawful selected argument codec. It does not introduce a
second interpreter, patch, post-state, or authority context.

`Theory.CanonicalTransition` materializes the patch exactly once. Every later receipt, history
entry, or physical handler must refer to the same pre/post state.

### Flat hyperedges

`Kernel.DeclaredHyperedge` executes a finite family of incidences against one canonical pre-state,
checks request-indexed joint authority and aggregate resource law, and projects an actual kernel
hyperedge. `Kernel.MultiCellHyperedge` is the publication carrier for exact multi-cell effects.

The construction replaces nested object/call semantics with one typed event. It does not prove
database atomicity by itself.

### Durable settlement

The durable model closes the semantic shape of compare-and-swap, nullifier insertion, exact
multi-cell charge, history append, idempotency, and crash behavior. A real deployment must supply
`ImplementationRefinement` for its physical state/step representation, transaction linearization,
WAL recovery, and replication/failover. It must also bind byte-size functions and tariff lanes to
actual versioned codecs. No liveness, fairness, availability, digest collision resistance, or
physical persistence follows from the model alone.

## Private, reactive, and external work

### Pure private computation core

The authoritative private-computation `CoreRequest` includes program/relation, canonical/native/
semantic input identities and a named bridge, output commitment, typed resource effects, footprint,
eager nullifier, and mode pins. It deliberately excludes observers, recipients, purpose, reveal,
declassification, release, and a second authority portal.

`ComputationCellEffect.Accepted` binds the lawful full-request digest and the lawful
`(resourceEffects, footprint, nullifier)` digest, exact pre-root, validated patch, and resource
realization. Its release carrier is empty and every accepted core effect is sealed. BFV's current
semantic core binds the exact program/relation/mode/input/output statement and all 384 equations.

Residual: concrete BFV codecs/digests/patch adapter, proof suite and controller, PCS/CR/ROM,
confidentiality/knowledge proof, shared-MPC dialects, and a later separately authorized disclosure
effect linked to the output commitment.

### Reactive lifecycle and tools

Reactive decisions are joined to canonical patches and expose exact roots/footprint. Refusal and
blocking preserve the pre-state. Physical commit remains a handler obligation.

The target UI/agent model is:

1. projections are pure typed programs returning their exact dependency set;
2. committed deltas invalidate precisely intersecting dependencies;
3. drafts carry a base root and cannot masquerade as committed state;
4. promises freeze a typed condition and continuation;
5. a wake receipt consumes a nullifier at most once; and
6. tools produce `Intent → Pending → Completed/Failed` events rather than a single magical call.

## Hyperdocuments: the semantic medium

Hyperdocuments are not a UI feature bolted onto receipts. They are a semantic/history family:

- typed document/schema/content identity;
- fields and explicit provenance-bearing conflicts;
- link and transclusion records with origin evidence;
- stable ranges under insert/delete/move and explicit death policy;
- marks and annotations separated from base content;
- causal events and exact parent heads;
- authenticated backlinks and retained history projections; and
- offline branches and conservative merge.

Landed **S/A** construction includes accepted content and version effects, atomic content+event
publication, exact causal parents, first-order link admission, exact-head history/finality indices,
finite injective multi-coordinate post layouts, proven ancestry, and merge publication. One field
source writes a typed value; two or more sources always store a `ConflictRecord`. A common base is
selected only from proof-relevant ancestry and can be ambiguous or absent.

Residuals include the complete run/element/field/conflict operation grammar, conflict resolution
policies, rights/views/search, checkpoints/GC, integration of base selection into richer merge
policies, concrete PCS/CR/ROM, physical persistence/finality, and migrated clients.

### Compound-document design analogy

DCOM/OLE, structured storage, and compound-document systems supply a useful comparison, not a
direct lineage claim. They assumed active embedding/linking, interface negotiation, marshaling,
remote activation/events, aggregation, and distributed commit. minidregg asks how to retain that
compositional ambition without ambient pointers, hidden mutation, location/configuration authority,
or runtime object identity:

- monikers → typed content-addressed references;
- structured storage → canonical sparse authenticated cells;
- embed/link → authenticated transclusion, backlinks, and history evidence;
- `QueryInterface` → explicit typed effect family/manifest clause, with no runtime object authority;
- proxy/stub marshaling → lawful codecs and generated bytes/error dispatch;
- aggregation → a flat typed multi-cell hyperedge;
- connection points → a verified reactive lifecycle; and
- distributed commit → the fail-closed multi-root/nullifier/budget/history journal model.

## Native proof and execution dialects

| Dialect | Current strongest boundary | Exact residual |
|---|---|---|
| Tower256 additive FRI | **A:** shared concrete Tower/cSHAKE/Merkle backend; arbitrary native bytes/error; Lean transcript, decoding, openings, folds, final polynomial, ideal-clause bridge, one controller coin | instantiate supplied failure cover, PositionBinding/CR, cSHAKE→ROM, far-word FS/proximity, executable checker, deployed codecs/IDs, end-to-end benchmark |
| Tower256 indexed LogUp | **A:** exact address/index semantics and gated two-byte-reply controller for clause 404 | clause 404 remains out of base/deployment; PCS/sampled decider, binding/CR/ROM, common-game/history join, mutable RAM, artifact work profile |
| BabyBear/Ext6 | **A:** exact descriptor/gate algebra and deterministic Lean transcript/algebra controller; seven-event conditional admission ledger | PCS, subfield proof, proximity, binding, ROM, final LDT, global game, recursion, deployed security |
| BFV/residue ring | **S/A arithmetic:** pure core and all 384 exact equations; native buffer candidate can be Lean-rechecked locally | proof suite/controller pins are zero; no confidentiality, knowledge, PCS/CR/ROM, concrete core codec/patch deployment, or history join |
| MPC/shared values | **S only:** generic sealed computation shape | concrete protocol/dialect, malicious security, abort/fairness, output binding, separately authorized threshold release |

Tower256 exists so binary semantics can use cheap native operations while sampling security-sized
challenges and opening into a large proof system. It is not a claim that all computation should be
interpreted as GF(2).

## Compiler, artifacts, and deployment

### Derived arithmetization

`Compiler/Air` proves the circuit fold and executor agree. `AirFlatten` derives a degree-≤2 gate
system with forced auxiliary wires. `Compiler/Emit` serializes a first-order descriptor and proves
descriptor satisfaction equivalent to the Lean gate system. `AirBignum` currently supplies exact
range-checked fixed-width addition. Multiplication and broader language lowering remain.

### Authenticated native catalog

The canonical artifact's encoding, content address, JSON, and generated Rust authenticate separate
native ABI codecs and a native work catalog. The current catalog contains Tower256 dot product work
`9101`, carrier profile `205`, request codec `9001`, and response codec `21`. Build generation takes
that authenticated catalog as its sole source; standalone JSON and embedded Rust payload are
byte-identical.

This authenticates declared transport identity only. Rust remains fallible opaque computation;
there is no Rust semantics, refinement, FFI proof, or cross-language correctness theorem.

### Honest deployment registry

`ComposableDeploymentManifest` derives admitted clause lists only from actual controller entries
and separately joins artifact, manifest, controller-registry, and native-catalog well-formedness.
Gated or reserved clauses cannot project into deployment.

- base V1: zero dialect clauses;
- clause 406: deterministic Lean controller implemented, no emitted Rust byte profile;
- clause 404: security-gated, exact extension-local dispatch exists, still absent from base and
  deployment; and
- BFV 901: reserved, with unclosed carrier and zero proof codec/suite/controller pins.

## History and Loom

Loom provides multiplicative and additive proximity results, claim folding, arbitrary-depth
extraction, sumcheck, Fiat–Shamir/RBR game structures, constrained masking, and explicit security
budgets. Published or external algebraic inputs remain named interfaces rather than being described
as locally proved.

The semantic history construction retains exact entries, predecessor/state links, clause evidence,
and one folded claim. The BCS history reduction reconstructs genesis, chain/link words, and
challenges from the retained trace; binds roots/opened columns to that exact transcript; and keeps
PCS, binding, and ROM `Good` events on one history coin. Exact finality is indexed by head, entry,
occurrence, and derived receipt root.

`SemanticHistoryTower256CheckpointGame` now joins that history predicate and the Tower256 additive
controller predicate on one `Omega`, one existing `FailureLedger`, exact terminal/initial root and
schedule equalities, and one four-event union bound without independence. Its family deliberately
requires the external BCS false-accept predicate/history reduction cover and the additive cover;
MCA and RS `codeExact` also remain premises.

Open **P** work: instantiate those covers with concrete PCS opening, commitment CR/binding, ROM
transport, MCA/error hypotheses, and hiding/sub-UD. The structural common game is landed; its
cryptographic premises are not.

## Consumer migration

The proof system does not subsume a kernel until consumers move. Required **D** demonstrations:

1. token authorization: one real capability/revocation/nullifier path;
2. DeOS/agent platform: one reactive view, invalidation, promise, and tool lifecycle;
3. Grains: one R3 causal chain and checkpoint;
4. Drex/FHEgg/Dark Bazaar: one sealed computation, resource settlement, and later release;
5. DreggCloud/DreggNet: one multi-resource command through a durable handler; and
6. hypermedia: one offline branch, authenticated transclusion/backlink, merge conflict, and current
   authority settlement.

Each adapter must map request, authority, state roots, effects, history, failure behavior, and
physical completion. Compatibility modules are migration views, not proof of cutover.

## Ordered frontier

1. Instantiate the landed additive/history common-game cover with concrete CR/ROM/proximity/PCS,
   MCA, code-exactness, and hiding prices.
2. Give Tower256 additive and lookup work complete versioned proof/container/domain codecs and
   artifact-native work identities; emit an executable Lean-owned checker boundary.
3. Instantiate a concrete Ext6 PCS/subfield/proximity/final-LDT controller and global ledger.
4. Deploy the pure private-computation core for one BFV consumer, then add disclosure as a separate
   authorized event.
5. Instantiate durable storage refinement for one consumer, including WAL recovery and tariffs.
6. Complete Hyperdocument operation grammar, authenticated transclusion/backlink maintenance, and
   one real offline merge UI.
7. Run matched **B** workloads against candidate external stacks and apply Loom's kill criteria.

## Performance and evidence discipline

The landed native benchmark at source `54295c6` and evidence `4d1f290` validates byte identity and
measures only generated work-9101 dispatch overhead: ratio `0.985–1.040` on hbox and
`0.985–1.025` on persvati for lengths 1–16384. It sets no threshold and proves no semantics.

Future benchmarks must use the actual admitted protocol and measure proof size, memory, checkpoint
cadence, tail latency, dense/sparse crossover, and CPU/SIMD/GPU kernels. Remote evidence uses exact
committed archives and isolated run trees through [`scripts/remote-check.sh`](scripts/remote-check.sh).

## Work discipline

Each step closes one edge in the composition graph:

1. state the exact relation and false neighboring claim;
2. land the theorem or Lean controller that owns the edge;
3. commit immediately in a thematic commit, green or not;
4. fix forward with a separate commit;
5. record exact residuals and maturity boundary; and
6. measure only a selected, admitted path.

No step adds a second semantic implementation in Rust. New native code is generated data/dispatch
or caller-parameterized opaque computation. Decisions with cross-layer consequences receive a
record under [`docs/decisions/`](docs/decisions/).

## Public-claim gate

A diagram or poster may describe the design today. A deployment claim requires:

- one canonical typed multi-cell turn through a real durable handler;
- two concrete Lean-owned proof controllers with priced security reductions;
- lookup/RAM linked to semantic columns and a real consumer;
- succinct history on the same security game as its checkpoint proof;
- sealed compute plus separately authorized disclosure; and
- matched committed-source performance evidence.

Until those conditions hold, the construction is an ambitious and increasingly concrete research
program—not a deployed universal kernel or completed proof system.
