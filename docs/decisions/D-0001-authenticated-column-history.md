# D-0001 — Typed authenticated columns and dual-root history

- Status: accepted
- Date: 2026-08-09
- Supersedes: separate per-clause commitment/opening seams

## Decision

Use one Lean-owned, multi-phase authenticated-column controller for commitments, transcript order,
openings, checked representation-equality edges, and terminal clause attestations. Keep witness
algebras heterogeneous. The first concrete backend is Tower256/additive LCH-FRI.

Semantic history uses a dual-root schedule: commit the exact link word before `gamma`; derive
`gamma`; then bind the next folded root. Only the terminal folded word enters the additive
checkpoint. WARP-shaped accumulation remains the semantic/history accumulator; additive FRI is its
checkpoint/PCS backend, not a replacement semantic accumulator. The retained-history BCS game now
reconstructs exact genesis/chain/link words and challenges and keeps its PCS, binding, and ROM
premises on one history coin. `SemanticHistoryTower256CheckpointGame` now joins that history
boundary to the Tower256 additive controller on one `Omega`, one existing ledger, exact root and
schedule equality, and one four-event bound without independence. The concrete BCS false-accept
predicate/history cover, additive cover, MCA/code-exactness, and cryptographic reductions remain
explicit family premises.

## Hard invariants and non-claims

- Lean owns transcript/control/acceptance; native calls return only bounded data or opaque errors.
- GF(2), Ext6, residue rings, and MPC shares are never coerced into a universal field.
- A representation bridge is a checked common-opening relation, not a cross-characteristic cast.
- Capacity-regime soundness is not assumed; deployed rates use only an explicitly proved regime.
- The landed Tower256 additive controller closes deterministic admission, not PCS/ROM/proximity
  security. The extension-local LogUp controller closes byte dispatch, not deployment.
- Until a concrete PCS, CR, and shared-ROM game instantiate the common cover, this is not a
  deployed succinct proof or security claim.

## Alternatives rejected

- One universal AIR/field: cannot preserve binary, odd-characteristic, and residue-ring semantics.
- A fourth bespoke WARP/PCS interface: repeats the same missing commitment/transcript object.
- Additive FRI as the per-turn accumulator: loses the stronger history/extraction structure.
- Shifted same-round root scoring: retains the adaptive increment/root-lag gap.

## Required evidence

- `Compiler.AuthenticatedColumnPlan`: typed roots-before-challenges executable controller.
- `Compiler.Tower256CshakeMerkleController` and the additive admission modules: exact shared
  cSHAKE/Tower/Merkle transcript, byte decoding, coherent openings/folds, and ideal-clause bridge.
- `Compiler.Tower256LogupClauseDispatch`: extension-local clause-404 first-order byte dispatch;
  clause 404 remains absent from base/deployment.
- `Assurance.SemanticHistoryWARPAdditiveJoin`: exact dual-root/history/checkpoint join.
- `Assurance.SemanticHistoryBcsGame`: exact retained-history BCS reconstruction and conditional
  single-coin ledger.
- Instantiate the landed common-game family with a concrete BCS predicate/cover,
  PositionBinding/CR price, cSHAKE→ROM transport, proximity/PCS reduction, MCA/code-exactness,
  sampled decider, and hiding schedule before a deployment claim.
- Remote evidence records must name the exact commit and command and may claim only that check.

## Revisit trigger

Revisit if a straight-line knowledge-sound, hiding PCS with strictly simpler typed composition
subsumes both WARP link attribution and additive checkpoints in the required transparent/PQ model.

## Current source anchors

- `Assurance/SemanticHistoryAccumulator.lean`
- `Assurance/SemanticHistoryStraightlinePcs.lean`
- `Assurance/SemanticAdditiveFriCheckpoint.lean`
- `Assurance/SemanticHistoryBcsGame.lean`
- `Assurance/SemanticHistoryTower256CheckpointGame.lean`
- `Compiler/Tower256CshakeMerkleController.lean`
- `Compiler/Tower256LogupClauseDispatch.lean`
- `Compiler/AdditiveFriReceiptClause.lean`
- `Compiler/Logup256ReceiptClause.lean`
