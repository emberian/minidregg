# The minidregg project

**Current design constitution — 2026-08-09**

This is the stable forward plan. [`GOAL.md`](GOAL.md) is the evidence ledger: it records what was
actually proved or implemented. This file records the system we are building, the invariants that
may not be traded away, and the order in which incomplete edges are closed.

## One sentence

minidregg is a proof-native semantic computer: one typed transactional/effect semantics, several
typed execution modes and algebra-native proof dialects, canonical proofs between representations, one receipt/event
relation, and one unbounded history accumulator.

It is deliberately **not** one universal field, AIR, VM, or cryptographic backend.

Here **native dialect** means native to an algebra or computation model (binary words, Ext6,
residue rings, or shares). It never means that Rust owns a semantics.

## The target composition

```text
indexed program + typed request + capabilities + observer policy
                              |
                              v
              authoritative transactional semantics
               (validate -> patch -> commit or reject)
                              |
                              v
        canonical ReceiptDelta + request/decision/effect events
             /                 |                    \
            v                  v                     v
   reactive projection     external intents      private execution
   and UI dependency DAG   and completions       MPC / FHE / ZK
            \                  |                     /
             v                 v                    v
         native dialect relations and representation proofs
       GF(2) words | Ext6 arithmetic | lookup/RAM | residue rings
                              |
                              v
              proof-verified semantic receipt relation
                              |
                              v
          hiding, knowledge-sound unbounded history accumulator
                              |
                              v
              optional final light-client compression
```

The common object is the **semantic receipt relation**, not a common witness field. A dialect
adapter proves that its native result realizes one typed receipt clause. The outer accumulator sees
those authenticated clauses and their canonical encodings; it never pretends that GF(2),
BabyBear, MPC shares, and an FHE residue ring are the same algebra.

## Invariants

1. **One declared denotation.** Executor, public view, receipt encoder, constraints, and explanation
   are derived interpretations of the same indexed program. Cross-carrier agreement is proved by
   fold fusion or a logical relation, not asserted by shared names.
2. **Lean owns semantics, control, and acceptance.** A handwritten Rust type, validator,
   transcript, scheduler, or verifier is never a semantic implementation and cannot be called a
   refinement: this project has no Rust operational semantics. Lean emits the descriptor,
   bytecode, codec, controller plan, and API. Rust is either mechanically generated DTO/dispatch
   glue or opaque untrusted compute behind that interface. A bad kernel may hurt availability,
   completeness, or speed; only Lean may decide the continuation or construct an accepted token.
3. **Patch, then commit.** A failed request cannot leave an unreceipted mutation. Charged refusal,
   if supported, is a distinct committed outcome with its own receipt.
4. **One admission judgment.** Every signature, capability, token, ZK proof, threshold decision, or
   attestation proves the same complete typed request. Evidence modes cannot bypass target,
   destination, freshness, policy, conservation, or footprint checks.
5. **Receipts are the reactive bus.** Projection invalidation, promises, wakeups, UI refresh,
   external tools, and agents react only to committed `ReceiptDelta`s. A best-effort event or
   in-memory mutation is not semantic state.
6. **Private state has an observer semantics.** Public, committed, selectively disclosed, shared,
   and encrypted values are modes of typed values. Reveal/declassification is an explicit effect
   justified by authority and recorded in the receipt.
7. **No implicit algebra cast.** Cross-characteristic and cross-modulus equality requires a
   canonical representation theorem: exact limbs and carries, range proofs, a named joint
   protocol, or a byte identity with deliberately byte-only meaning.
8. **Roots precede challenges.** Every lookup, fold, query schedule, opening, and extraction game
   fixes the relevant commitments before its random challenges.
9. **Security regimes are values.** Unique, Johnson, finite-step post-Johnson, and exponential-
   budget post-Johnson are distinct settings. Capacity is not a deployed soundness setting.
10. **Claims follow composition.** Passing component tests, having a wide root carrier, or proving
   an ideal theorem never silently upgrades an end-to-end security label.

## Semantic machine

The kernel is an indexed free program with response-dependent typestate. Primitive operations
declare their request/response types, effect row, footprint, guard, patch semantics, resource
delta, authority demand, privacy policy, and evidence relation. The load-bearing transition is:

```text
run : State i -> Program i j A -> Handler effects
   -> Reject error attemptedReceipt
    | Commit (result, State j, ReceiptDelta)
```

State roots are computed from canonical materialization. They are not independently mutable cache
fields. A transaction with several cells/resources is accepted only as one bound object with a
shared turn id, exact indexed resource balance, complete authority, freshness, and one atomic
combined patch.

The first formal substrate is already present in:

- [`Theory/IndexedProgram.lean`](Theory/IndexedProgram.lean): indexed syntax, interpretation,
  cross-carrier fusion, and relational folds;
- [`Theory/TypedAuthorization.lean`](Theory/TypedAuthorization.lean): request-indexed evidence,
  attenuation, epochs, ancestry, and revocation;
- [`Theory/AuthorizationDeclaration.lean`](Theory/AuthorizationDeclaration.lean) and
  [`Theory/EffectDeclaration.lean`](Theory/EffectDeclaration.lean): first-order executable plans
  whose successful tokens carry exact-request authority, footprint, and balance proofs;
- [`Theory/DeclaredTurn.lean`](Theory/DeclaredTurn.lean): derives the complete request from one
  request seed, typed effect declaration, and canonical pre-state, runs authorization before
  effects, derives both roots, and makes rejection materialize to the exact pre-state;
- [`Theory/CellState.lean`](Theory/CellState.lean): logical state, canonical materialization, and
  validated-only patches make root coherence, frame, rejection atomicity, and no-ghost state
  structural;
- [`Theory/PrivacyProfile.lean`](Theory/PrivacyProfile.lean): observer-indexed privacy vocabulary;
- [`Theory/DisclosureDeclaration.lean`](Theory/DisclosureDeclaration.lean) and
  [`Theory/PrivateComputationDeclaration.lean`](Theory/PrivateComputationDeclaration.lean):
  same-opening, authorization, named representation bridges, and explicit ZK/MPC/FHE reveal or
  declassification effects;
- [`Theory/ReactiveReceipt.lean`](Theory/ReactiveReceipt.lean): frame-preserving receipt deltas,
  dependency-indexed lenses, drafts, and witness cursors;
- [`Theory/GuardedAdvice.lean`](Theory/GuardedAdvice.lean): guarded external advice without
  laundering an unproved value into the kernel;
- [`Theory/ReactiveCellTransition.lean`](Theory/ReactiveCellTransition.lean): joins the existing
  reactive controller to validated cell patches, proves exact request/root/footprint bindings and
  frame laws, and releases a logical post-cell only behind an explicit physical CAS/nullifier
  receipt premise;
- [`Theory/TurnTransition.lean`](Theory/TurnTransition.lean): preserves ordinary declared and
  resumed reactive indices in one typed sum, delegates to their existing Lean controllers, and
  exposes common canonical roots, exact footprint, `ReceiptDelta`, and frame facts without claiming
  history admission or physical commit;
- [`Compiler/SemanticManifest.lean`](Compiler/SemanticManifest.lean),
  [`Compiler/SemanticArtifactBundle.lean`](Compiler/SemanticArtifactBundle.lean), and
  [`Compiler/NativeKernelPlan.lean`](Compiler/NativeKernelPlan.lean): content-addressed first-order
  declaration/phase artifacts and fallible native work whose opaque errors block and whose bounded
  successful results are checked only by Lean-owned control;
- [`Compiler/MinidreggV1ArithmeticWork.lean`](Compiler/MinidreggV1ArithmeticWork.lean): an inhabited
  one-instruction arithmetic extension (clause `406`) whose concrete `0+0=0` response reaches the
  generic Lean certificate, while a native error reaches only the blocked outcome;
- [`Compiler/DeclaredEffectArtifact.lean`](Compiler/DeclaredEffectArtifact.lean) and
  [`Compiler/MinidreggV1Artifact.lean`](Compiler/MinidreggV1Artifact.lean): the concrete typed
  account-move projection derived from `EffectDeclaration.Declaration.toWire.words` and the closed
  V1 JSON artifact at [`prover/testdata/semantic_artifact_v1.json`](prover/testdata/semantic_artifact_v1.json);
- [`Compiler/NativeGlueGen.lean`](Compiler/NativeGlueGen.lean) and
  [`Compiler/MinidreggV1NativeGlue.lean`](Compiler/MinidreggV1NativeGlue.lean): deterministic
  generation of [`prover/generated/semantic_artifact_v1.rs`](prover/generated/semantic_artifact_v1.rs),
  containing constants, DTOs, and opaque work-dispatch methods only—no semantic validator,
  transcript, verifier Boolean, or acceptance token. The generated file is compiled by
  `prover/src/lib.rs`, but no dispatch implementation currently connects its requests to kernels;
- [`Assurance/DeclaredTurnReceipt.lean`](Assurance/DeclaredTurnReceipt.lean): defines the
  declaration-indexed `DeclaredEffect`, derives the sole executable receipt core from
  `DeclaredTurn.execute`, proves commit/reject validity, and fixes the `SemanticTurnReceipt` and
  history-claim cores to that execution; manifest/header/code-membership entry obligations remain;
- [`Assurance/PrivateComputationReceiptClause.lean`](Assurance/PrivateComputationReceiptClause.lean):
  turns an existing typed private-computation `Completion` into a request-bound disclosure event,
  records it only on a committed turn, and binds its dialect and representation bridges as manifest
  facts without assigning cryptographic meaning to a native suite;
- [`Assurance/SemanticHistoryStraightlinePcs.lean`](Assurance/SemanticHistoryStraightlinePcs.lean):
  states the same-carrier, prefix-typed fold-root and one-transcript PCS extraction interface,
  derives exact semantic-head recovery through the existing erasure theorem, and keeps the
  knowledge-soundness and binding/ROM prices explicit rather than claiming a WARP instantiation.

## Native dialects

| Dialect | Native work | Current proof direction | Boundary that must stay explicit |
|---|---|---|---|
| **GF(2) towers** | Boolean control, words, hashes, bitwise code, binary MLEs | `GF(2^64)`/`GF(2^256)` algebra and additive LCH/FRI; `BinaryTowerFanPaarCodec` fixes exact recursive low/high coordinates and a 32-byte little-endian codec; `Compiler.AdditiveFriReceiptClause` binds basis order, affine domain, rate schedule, roots-before-challenges, coherent queries, and the exact ideal UD predicate/bound | Rust retains opaque arithmetic/transform/hash buffers, but its four-limb tower/LCH implementation and chosen hash algorithm are not yet generated or checked against the Lean codec. The concrete commitment/CR, cSHAKE-ROM transport, buffer checking, controller instance, and outer accumulator remain; the generic clause is not base-V1 admitted |
| **BabyBear / Ext6** | Prime-field arithmetic, emitted degree-2 gates, selectors | Lean proves `X^6−31` irreducibility, descriptor provenance, seven factored operands, degree-two rounds, terminal affine functionals, and eta aggregation | Base V1 deliberately admits no Ext6 or other proof dialect. Native `field6` limb/polynomial conventions are not connected to generated pins. A concrete Ext6 clause/controller, commitment/transcript/opening control, coherent proximity, subfield provenance, final LDT, and CR/ROM composition remain |
| **Lookup / RAM** | Range, decode, tables, sparse state buses | `LogupIndexLink` proves canonical Boolean addresses and exact pushforward; `Compiler.Logup256ReceiptClause.indexedTableReceiptClause` derives the exact indexed evaluation behind explicit Tower256/PCS/CR/ROM premises; the profile uses the proved recursive Fan–Paar codec; native Tower256 retains generic arithmetic kernels only | V1 declares distinct `gf2Tower256Carrier` profile `205`, degree `256`, and codec `21`; clause `404` selects it only in a local extension. The former handwritten LogUp round-polynomial APIs are deleted; `tower256_kernels` accepts only caller-selected generic buffers/indices/coordinates. Its four-`u64` representation remains unverified compute. PCS, CR/ROM, controller admission, proximity, and mutable state remain |
| **Residue-ring FHE** | BFV/BGV/TFHE arithmetic, RNS/NTT, key switching | Bignum/cross-modulus theory plus `Compiler.BfvReceiptClause`; `Assurance.BfvNativeBufferAdmission` uses a fallible opaque runner, checks the emitted per-row scalar/accumulator descriptor and exact links in Lean, constructs all 384 rows under an inhabited local controller binding, and projects the private receipt event with every exact `Int` equation | The proof-suite pin remains unassigned. Arithmetic admission is real; privacy/knowledge soundness, commitment binding, generated deployment dispatch, and the full application receipt remain; naive field lookup over cyclotomic rings is unsound |
| **MPC / shared values** | Collaborative private turns and threshold outputs | Typed share/transcript receipt adapter | Malicious security, abort/fairness, and public output binding are separate from local proof soundness |

Tower256 exists because it lets binary semantics use cheap native operations while sampling
security-sized challenges and bridging evaluations into a large-field PCS. It is not an attempt to
interpret all computation as GF(2).

The remaining handwritten kernels are not yet uniformly convention-free. The protocol-shaped
`logup256_kernels` round-message/interpolation surface has been deleted; its surviving generic
arithmetic is `tower256_kernels`. `hash_kernels` fixes only the cSHAKE256 algorithm, and the
tower/Ext6 modules fix limb and polynomial representations. Lean now fixes the Tower256 recursive
Fan–Paar semantic basis and codec exactly; Rust's four-limb realization of it is still not proved or
generated. Until native conventions are checked against exact Lean-owned pins, they are opaque
untrusted candidate computation and may affect only availability/completeness—not semantics or
acceptance.

The Tower256 carrier distinction is load-bearing: a clause whose arithmetic premise is over
`GF(2^256)` cannot be registered on the degree-64 `gf2Carrier`. V1 now includes
`gf2Tower256Carrier` (profile `205`, degree `256`, distinct codec `21`) in Lean, JSON, and generated
Rust artifact data, and clause `404` selects it. The clause itself is still extension-only, and
`BinaryTowerFanPaarCodec` proves the Lean profile's recursive coordinates and 32-byte codec. Neither
carrier metadata nor that semantic theorem proves that the four-`u64` native `Tower256`
representation implements the profile.

## Receipt relation

A receipt binds at least:

- semantic/program/policy/proof-suite identifiers;
- the complete typed request and subject/target/federation/nonce/epoch context;
- pre/post roots and an exact touched-resource footprint;
- authority evidence, lineage, current epochs, revocation and nullifier facts;
- ordered effects and full-width resource deltas;
- observer/declassification events;
- native dialect statements, commitment roots, and bridge statements;
- external intent and later completion/result receipts;
- either `Commit post` or `Reject` with the atomicity claim `post = pre` (unless the rejection is
  explicitly a charged committed transition);
- prior receipt/history links and verifiable finality when finality is claimed.

The handwritten `prover/src/semantic_receipt.rs` ABI prototype is deleted. Its replacement spine
begins with a Lean-owned `SemanticManifest`, the canonical V1 artifact, generated native DTO
glue. Native code receives bounded calls and returns data; it neither constructs nor verifies
receipt meaning, and `DialectClauseDispatch` requires a matching Lean controller registry before a
clause can be resolved. Registry records named `DialectClauseDecl` are first-order pins, not claims
that a native proof system or verifier exists. Base V1 therefore carries no dialect declarations.
The generated Rust file is compiled into the `prover`
crate as artifact data and a trait surface, but it is not a live dispatch integration.

[`Assurance/SemanticReceiptRelation.lean`](Assurance/SemanticReceiptRelation.lean) owns the first
common accumulator language: a fixed pre/post/touched word, Boolean-mask and frame quadratics, an
iff theorem recovering exactly `ReceiptDelta`, and a native Loom `AccClaim` fold. The remaining
semantic wrapper is now [`Assurance/SemanticTurnReceipt.lean`](Assurance/SemanticTurnReceipt.lean):
commit requires authorization indexed by the exact request, exact effect-digest and effect-to-delta
semantics, permitted disclosures, and bound pre/post roots; reject has no post-state. The wrapper
projects to the accumulator nucleus only after those clauses are proved.
The former Rust receipt-relation mirror and proof-history wrappers have been deleted.
[`Assurance/SemanticReceiptRuntimeCodec.lean`](Assurance/SemanticReceiptRuntimeCodec.lean)
proves the exact `16 binding cells ++ 3*k+slot` layout, injectivity of the fixed 32-byte/u16
packing, both residual lanes, and the bound `AccClaim` fold. Runtime
[`Compiler/SemanticTurnReceiptDescriptor.lean`](Compiler/SemanticTurnReceiptDescriptor.lean)
projects the existing Lean relation through the existing AIR/emit path, proves descriptor
acceptance iff the authoritative bound relation, and emits the field/layout/tag/constraint
artifact. The handwritten Rust typed-turn verifier and lookup receipt adapter were deleted; no
native module may reconstruct those decisions. Full authorization/effect/disclosure/header-preimage
arithmetization and emitted online control remain.

`Theory.DeclaredTurn` now supplies the executable typed transaction boundary: request effect digest
and pre-root are derived, authorization precedes the effect checker, commit carries the
request-indexed `AuthorizedEffect`, post-root is recomputed, and rejection is definitionally the
pre-state. `Compiler.DeclaredEffectArtifact` projects the concrete typed account move through
`Declaration.toWire.words`; the old `Effects.EffectSpec` descriptor is not the semantic effect
declaration. `Assurance.DeclaredTurnReceipt` names the resulting `DeclaredEffect`, defines
`executeCore` with no caller-authored receipt witness, and proves `canonical_core_exact` and
`historyClaim_core_exact` through the existing turn-receipt/history spine. This closes the semantic
core join, not the complete canonical header controller: manifest well-formedness, exact header
projection, code membership, reactive admission, complete dialect-clause control, and emitted online
admission remain. `Assurance.PrivateComputationReceiptClause` separately closes one disclosure
edge: a typed private `Completion` becomes a manifest/mode/request-bound `ReceiptEvent`, and
`recordCompletion` can attach it only to a committed turn. Its abstract portal evidence and
registry pins are not cryptographic verification.

## Reactive UI and tools

The good idea from Breadstuffs/DeOS is retained. The target is to collapse the previously separate
worlds onto the receipt relation. `ReactiveReceipt`, `GuardedAdvice`, `ReactiveController`, and
`CellState` are joined by `ReactiveCellTransition`: controller acceptance is rechecked against the
validated cell patch, exact roots and footprint are exposed, and blocked/rejected outcomes preserve
the pre-cell. Durable mutation remains outside Lean behind the explicit `HandlerPremise` binding one
atomic CAS/nullifier receipt. `TurnTransition` supplies one typed ordinary/resumed control surface
and common `TransitionFacts`; by design it contains neither history admission nor physical commit.
The tool/UI/agent join remains:

1. a projection is a pure, proved program from semantic state and observer policy to a typed view;
2. it returns the exact dependency set used to produce that view;
3. a committed `ReceiptDelta` invalidates precisely the intersecting dependencies;
4. drafts/speculation carry an explicit base root and never masquerade as committed state;
5. promises freeze a typed condition and continuation; a fill receipt supplies advice; a wake
   receipt consumes a nullifier and runs at most once;
6. external tools emit an intent receipt, then a separate completion/refusal receipt. Admission is
   not evidence that the side effect happened;
7. snapshots bind history head, state root, projection id/version, observer policy, lens, focus, and
   cursor. Rehydration refuses a mismatched history rather than selecting by height alone.

This supports local reactive UIs, server-rendered views, agents, workflows, and capability-gated
tools without creating separate unaudited state machines for each host.

## History accumulation

The target outer layer is a WARP-shaped hash/ROM accumulator over the stable semantic receipt
relation: unbounded depth, straight-line knowledge soundness, linear prover/decider, and logarithmic
verification for a suitable linear code. WARP currently has no ZK; hiding and simulation-
extractable receipt composition are separate wrappers, not prose properties of the accumulator.

The implementation sequence is:

1. **Dialect proof adapters.** Every accepted receipt clause is backed by a concrete Lean-owned
   verifier/controller. `AdditiveFriReceiptClause` owns the ideal characteristic-two clause and
   exact bound; `Logup256ReceiptClause` owns the indexed lookup semantic conclusion behind named
   external PCS/CR/ROM premises. Neither is yet an admitted base-V1 online controller. The Ext6
   manifest entry remains only a pin. Concrete controllers/artifacts, mutable RAM, and FHE follow.
2. **Stable common relation.** The pre/post/touched frame nucleus, typed request/auth/effect/
   disclosure wrapper, header-bound runtime word, and `AccClaim` fold have landed. A proof-relevant
   `SemanticHistoryAccumulator` admits commit/reject entries, enforces predecessor/state links, and
   reaches Loom's exact full-opening decider at arbitrary constructed depth. `DeclaredTurnReceipt`
   now fixes its receipt core to declared execution, and `PrivateComputationReceiptClause` records a
   typed completion as a request-bound committed disclosure. The lookup semantic clause has landed,
   but its external premises and integration into the base V1 manifest/controller remain.
   `SemanticManifest` owns the first-order content-addressed ABI; admit only closed clauses whose
   Lean controllers recheck their complete boundaries.
3. **One honest outer accumulator.** `SemanticHistoryStraightlinePcs` now pins the WARP-shaped
   interface: same carrier/index, prefix-only roots, literal fold commitments, one-transcript
   extraction, and an explicit error ledger. It does not construct the PCS, `Reduction`,
   `KStateFn`, Fiat–Shamir ROM, Merkle CR, or lagged-root hiding schedule. Instantiate those pieces
   and a sampled decider before replacing the retained-entry/full-opening seam or calling history
   succinct; do not name a structural hash chain an accumulator.
4. **Privacy composition.** Add hiding commitments/ZK adapters and prove the shared-ROM and
   simulation/extraction composition.
5. **Checkpoint compression.** Use additive RS/LCH or the selected code-switch PCS at explicit
   checkpoints. This is a light-client optimization, not the per-turn semantic kernel.

## Work discipline

Each development step closes **one edge in the composition graph**:

1. state the exact relation and the false neighboring claim;
2. land the formal theorem or Lean-emitted controller that owns that edge;
3. commit that thematic edge immediately, whether or not the tree is green;
4. add a focused substitution/refutation tooth when it advances the construction, then commit the
   fix forward instead of holding unrelated work for a test gate;
5. update [`GOAL.md`](GOAL.md) with evidence and this document only when a design decision changes;
6. defer broad test matrices, benchmarks, and presentation work until a complete path exists.

Commits are the development journal: small, thematic, frequent, and never delayed for a broad
verification ritual. A later compile or theorem failure becomes a new fix-forward commit.

Cross-layer or expensive architectural choices additionally receive a compact record under
[`docs/decisions/`](docs/decisions/). The decision names its hard invariants, rejected alternatives,
required evidence, and invalidation trigger; routine theorem work still needs only a thematic
commit. Formal and remote evidence must identify the exact source commit and may support only its
stated claim ceiling.

No step may add a second semantic implementation in Rust. New Rust is either generated data-only
glue or a clearly labeled, caller-parameterized opaque compute kernel invoked through a
Lean-emitted interface. It is never a refinement and never returns the project's acceptance bit.

`Compiler.SemanticController.arbitraryOracle_integrity` now establishes that rule for the current
fixed frame-nucleus descriptor model: for every
arbitrary native oracle, reaching the sole Lean `Verified` constructor implies exact-request
authorization, the existing bound receipt relation, and acceptance by the Lean-emitted descriptor.
Native failure can deny availability or completeness; it cannot construct an accepted turn.

Performance work begins on the actual selected protocol. Distributed hosts (`persvati`, `hbox`)
are used for genuinely expensive builds or measurements through
[`scripts/remote-check.sh`](scripts/remote-check.sh): an exact committed archive, unique run tree,
resource limits, and hashed evidence. Their pre-existing minidregg directories are never source
worktrees. See [`D-0003`](docs/decisions/D-0003-remote-evidence.md).

## Ordered frontier

1. Derive the canonical receipt/history entry from `DeclaredHyperedge.CommittedHyperedge`; project
   authorization state from the same canonical pre-state; compile ordinary, reactive, private, and
   external-intent/completion effects into that common carrier. The current compatibility sums are
   migration views, not the future kernel.
2. Instantiate one Tower256/additive `AuthenticatedColumnPlan` with the landed concrete Lean codec,
   a native byte-decoding/recheck boundary, commitment,
   cSHAKE/Merkle, PCS, transcript/ROM/CR reduction, and sampled decider. The exact commitment/opening
   adapter, attestation-to-WARP message bridge, and attestation-to-indexed-LogUp semantic bridge have
   landed; next instantiate the real lookup/proximity controller and use the same accepted transcript
   to discharge the WARP/additive history checkpoint under one game.
3. Close the unshifted WARP claim reindexing and one common security game, then remove the
   retained-entry/full-opening history seam only after the succinct path is real.
4. Join verified deltas to promises, DeOS projections/invalidation, and typed external
   `Intent → Pending → Completed/Failed` receipts without claiming physical handlers are proved.
5. Close the BFV/RNS native-ring proof/controller and common-opening representations, then add
   malicious MPC session evidence and separately authorized threshold release.
6. Migrate one authorization/capability path, one DeOS reactive path, one Grain R3 chain, one
   DreggCloud command, and one DreggNet funded lease/settlement before claiming kernel subsumption.
7. Benchmark the completed protocol against matched Plonky3/Binius/Flock/Mina workloads and apply
   the `D-0004` Loom kill criteria before producing the public poster.

## Poster gate

The poster is ready when all of the following are true:

- a typed semantic turn produces a canonical `ReceiptDelta`;
- at least two Lean-owned dialect-clause controllers verify real statements and cannot be spliced;
- one lookup/RAM path is linked to semantic columns rather than caller-chosen metadata;
- a multi-node receipt history is genuinely accumulated or compressed, not merely hashed;
- the privacy, FHE, and external-tool stories identify executable receipt boundaries;
- every performance/security number names its exact regime and assumptions.

Until then, diagrams in this document are engineering targets, not deployment claims.
