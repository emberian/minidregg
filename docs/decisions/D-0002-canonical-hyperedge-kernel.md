# D-0002 — Canonical cell effects and hyperedge turns

- Status: accepted
- Date: 2026-08-09
- Supersedes: Mina-derived call-forest execution as the future kernel carrier

## Decision

The semantic kernel is one canonical typed cell state plus flat accepted effect incidences. Each
effect binds the full authorization request, exact pre-state root, evidence, footprint/delta, and a
validated canonical patch. A prepared turn contains no parallel store or caller-supplied root.

Joint turns are finite N-incidence hyperedges over one canonical pre-state and shared apex. Every
leg is authorized against that same state; patches compose only under explicit disjointness or a
proved conflict algebra; aggregate full-width resource delta is checked once; one post-state and
receipt are committed atomically. This replaces the Mina call forest without discarding dregg2's
cell/effect/reactive ideas.

Private ZK/MPC/FHE execution is an accepted cell effect. Sealed output is the default; release or
declassification is a separate authorized effect. Reactive resumption is likewise an accepted
effect, not another nesting carrier.

## Hard invariants and non-claims

- Canonical materialization derives roots; roots are never independently mutable fields.
- Rejected and blocked decisions expose no post-state mutation or disclosure.
- Authorization state must be a projection of the same canonical pre-state.
- Durable compare-and-swap/nullifier insertion is an explicit external handler boundary; a Boolean
  `atomic` field is not proof of physical atomicity.
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
- `Kernel.DeclaredHyperedge`: executable N-incidence admission and nonzero-balance rejection.
- Receipt/history projection derived from those accepted objects, followed by compiler adequacy.

## Revisit trigger

Revisit the flat hyperedge carrier only if a real dependency calculus requires nested causality that
cannot be represented by named inputs, exact footprints, serial patch composition, and explicit
parent receipt edges.

## Current source anchors

- `Theory/TypedAuthorization.lean`
- `Theory/EffectDeclaration.lean`
- `Theory/CellState.lean`
- `Theory/ReactiveController.lean`
- `Theory/DeclaredTurn.lean`
- `Kernel/Turn.lean`
- `Kernel/TurnBalancedLimit.lean`

