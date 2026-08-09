# The minidregg project

**Current design constitution — 2026-08-09**

This is the stable forward plan. [`GOAL.md`](GOAL.md) is the evidence ledger: it records what was
actually proved or implemented. This file records the system we are building, the invariants that
may not be traded away, and the order in which incomplete edges are closed.

## One sentence

minidregg is a proof-native semantic computer: one typed transactional/effect semantics, several
native execution and proof dialects, canonical proofs between representations, one receipt/event
relation, and one unbounded history accumulator.

It is deliberately **not** one universal field, AIR, VM, or cryptographic backend.

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
2. **Lean owns semantics.** A handwritten Rust type, validator, transcript, or verifier is never a
   semantic implementation and cannot be called a refinement: this project has no Rust operational
   semantics. Lean emits the descriptor, bytecode, codec, and API. Hand-optimized Rust is
   unverified compute behind that generated interface; a bad kernel may hurt completeness or speed,
   but a Lean-derived verifier must prevent it from creating a false accepted receipt.
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
- [`Theory/PrivacyProfile.lean`](Theory/PrivacyProfile.lean): observer-indexed privacy vocabulary;
- [`Theory/ReactiveReceipt.lean`](Theory/ReactiveReceipt.lean): frame-preserving receipt deltas,
  dependency-indexed lenses, drafts, and witness cursors;
- [`Theory/GuardedAdvice.lean`](Theory/GuardedAdvice.lean): guarded external advice without
  laundering an unproved value into the kernel.

## Native dialects

| Dialect | Native work | Current proof direction | Boundary that must stay explicit |
|---|---|---|---|
| **GF(2) towers** | Boolean control, words, hashes, bitwise code, binary MLEs | `GF(2^64)` execution, `GF(2^256)` challenges, additive LCH/FRI, trace-linear retirement | Rust kernels are unverified compute; generated Lean authority, CR/ROM composition, and an outer large-challenge accumulator remain |
| **BabyBear / Ext6** | Prime-field arithmetic, emitted degree-2 gates, selectors | Factored gate sumcheck and sampled committed-trace opening | Coherent proximity, subfield provenance, and Lean-owned control that rechecks native compute |
| **Lookup / RAM** | Range, decode, tables, sparse state buses | `LogupIndexLink` proves canonical Boolean addresses, unit-vector incidence, and the exact pushforward; Tower256 Rust remains an unverified compute prototype | Lean emission of the lookup clause/bundle, CR/ROM/proximity, and the later Twist/Shout mutable-state layer remain; the handwritten Rust semantic adapter was deleted |
| **Residue-ring FHE** | BFV/BGV/TFHE arithmetic, RNS/NTT, key switching | Exact bignum/cross-modulus equations and ring-native receipts | Naive field lookup over cyclotomic rings is unsound; canonical limbs/ranges or indexed ring protocols are mandatory |
| **MPC / shared values** | Collaborative private turns and threshold outputs | Typed share/transcript receipt adapter | Malicious security, abort/fairness, and public output binding are separate from local proof soundness |

Tower256 exists because it lets binary semantics use cheap native operations while sampling
security-sized challenges and bridging evaluations into a large-field PCS. It is not an attempt to
interpret all computation as GF(2).

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

The handwritten `prover/src/semantic_receipt.rs` ABI prototype is deleted. Its replacement is a
Lean-owned `SemanticManifest`: native code will
receive bounded calls and return data; it will not construct or verify receipt meaning.

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

## Reactive UI and tools

The good idea from Breadstuffs/DeOS is retained, but the previously separate worlds are collapsed
onto the receipt relation:

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

1. **Native proof adapters.** Every accepted receipt clause is backed by a concrete verifier. The
   Lean relations for gates and indexed lookup have landed; their former handwritten native
   verifier adapters were deleted. Lean-owned clause controllers and emitted artifacts come next;
   mutable RAM and FHE adapters follow.
2. **Stable common relation.** The pre/post/touched frame nucleus, typed request/auth/effect/
   disclosure wrapper, native lookup clause, header-bound runtime word, and `AccClaim` fold have
   landed. `SemanticManifest` now owns the first-order content-addressed ABI; emit its concrete
   codec/API and admit only manifest-closed clauses.
3. **One honest outer accumulator.** Implement the WARP/FACS-style relation, transcript, decider,
   and extractor. Do not name a structural hash chain an accumulator.
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

No step may add a second semantic implementation in Rust. New Rust is either generated glue or a
clearly labeled unverified computational kernel invoked through a Lean-emitted interface.

`Compiler.SemanticController.arbitraryOracle_integrity` now makes that rule semantic: for every
arbitrary native oracle, reaching the sole Lean `Verified` constructor implies exact-request
authorization, the existing bound receipt relation, and acceptance by the Lean-emitted descriptor.
Native failure can deny availability or completeness; it cannot construct an accepted turn.

Performance work begins on the actual selected protocol. Distributed hosts (`persvati`, `hbox`)
are used for genuinely expensive builds or measurements, not repetitive ritual.

## Ordered frontier

1. Extend the landed Lean semantic-receipt artifact from the frame nucleus to the complete typed
   request, authorization, effects, disclosures, native clauses, and header preimage; emit online
   control from the same declaration.
2. Implement one real unbounded outer accumulation step and decider with its extraction statement.
3. Join `ReceiptDelta` to promises, UI projections, and tool completion receipts in the executable
   semantic machine.
4. Add the residue-ring/FHE receipt adapter through exact limbs, carries, ranges, and canonical
   cross-modulus equality.
5. Add hiding/ZK and collaborative/MPC adapters under the same typed request and receipt relation.
6. Only then optimize, benchmark against Plonky3/Binius/Flock/Mina, and produce the public poster.

## Poster gate

The poster is ready when all of the following are true:

- a typed semantic turn produces a canonical `ReceiptDelta`;
- at least two native dialect adapters verify real statements and cannot be spliced;
- one lookup/RAM path is linked to semantic columns rather than caller-chosen metadata;
- a multi-node receipt history is genuinely accumulated or compressed, not merely hashed;
- the privacy, FHE, and external-tool stories identify executable receipt boundaries;
- every performance/security number names its exact regime and assumptions.

Until then, diagrams in this document are engineering targets, not deployment claims.
