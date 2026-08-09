# D-0002 — Canonical cell effects and hyperedge turns

- Status: accepted
- Date: 2026-08-09
- Supersedes: Mina-derived call-forest execution as the future kernel carrier

## Decision

The semantic kernel is one canonical typed cell state plus flat accepted effect incidences. Each
effect binds the full authorization request, exact pre-state root, evidence, footprint/delta, and a
validated canonical patch. The common binding includes a family-selected lawful first-order
argument projection and exact `argsDigest` equality. Digest equality reflects arguments only under
an explicit binding/CR premise. A prepared turn contains no parallel store or caller-supplied root.

Joint turns are finite N-incidence hyperedges over one canonical pre-state and shared apex. Every
leg is authorized against that same state; patches compose only under explicit disjointness or a
proved conflict algebra; aggregate full-width resource delta is checked once; one post-state and
receipt are committed atomically. This replaces the Mina call forest without discarding dregg2's
cell/effect/reactive ideas.

Private ZK/MPC/FHE execution is an accepted cell effect. Sealed output is the default; release or
declassification is a separate authorized effect. Reactive resumption is likewise an accepted
effect, not another nesting carrier.

Durable settlement is modeled as fail-closed root compare-and-swap, nullifier insertion, exact
multi-cell charge, history append, idempotency, and crash outcomes. This semantic model is not a
claim about a database: each deployment must instantiate its physical state/step refinement.

## Hard invariants and non-claims

- Canonical materialization derives roots; roots are never independently mutable fields.
- Rejected and blocked decisions expose no post-state mutation or disclosure.
- Authorization state must be a projection of the same canonical pre-state.
- Durable compare-and-swap/nullifier insertion is an explicit external handler boundary. A
  deployment refinement must cover transaction linearization, WAL recovery, and any replication or
  failover; a Boolean `atomic` field is not proof of physical atomicity.
- Multi-cell charging is Lean-derived under an explicit cost policy, but byte sizes, base lanes,
  versioned codecs, and tariffs remain deployment bindings.
- Generic opaque-event append is deliberately non-semantic. Exact history adapters preserve their
  existing indexed receipt or joint-commit relations.
- No liveness, fairness, availability, digest collision resistance, or persistence is inferred.
- UI projections are observer-indexed pure views advanced from verified deltas.

## Alternatives rejected

- Preserve the call forest: retains Mina-specific execution topology as semantic authority.
- Add private/reactive branches to `TurnTransition.Mode`: grows a compatibility sum instead of a
  common kernel.
- Augment an already committed turn with a private receipt event: does not make private computation
  part of transition semantics.
- Maintain separate uniform and typed stores joined only by root equality: permits semantic drift.

## Required evidence

- `Theory.CanonicalTransition`: one canonical prepared transition and exact delta/frame laws.
- `Theory.AcceptedCellEffect`: common authorization/evidence/validated-patch join.
- `Theory.AcceptedCellEffectRequestBinding`: exact lawful argument-digest binding.
- `Kernel.DeclaredHyperedge`: executable N-incidence admission and nonzero-balance rejection.
- `Kernel.MultiCellHyperedge` and Hyperdocument publication: actual two-cell accepted publication.
- The durable commit model and success tooth, followed by one real physical
  `ImplementationRefinement` and consumer cutover.

## Revisit trigger

Revisit the flat hyperedge carrier only if a real dependency calculus requires nested causality that
cannot be represented by named inputs, exact footprints, serial patch composition, and explicit
parent receipt edges.

## Current source anchors

- `Theory/TypedAuthorization.lean`
- `Theory/EffectDeclaration.lean`
- `Theory/CellState.lean`
- `Theory/ReactiveController.lean`
- `Theory/AcceptedCellEffectRequestBinding.lean`
- `Theory/DeclaredTurn.lean`
- `Kernel/Turn.lean`
- `Kernel/TurnBalancedLimit.lean`
- `Kernel/MultiCellHyperedge.lean`
- `Kernel/DurableCommitProtocol.lean`
