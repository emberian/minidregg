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
checkpoint/PCS backend, not a replacement semantic accumulator.

## Hard invariants and non-claims

- Lean owns transcript/control/acceptance; native calls return only bounded data or opaque errors.
- GF(2), Ext6, residue rings, and MPC shares are never coerced into a universal field.
- A representation bridge is a checked common-opening relation, not a cross-characteristic cast.
- Capacity-regime soundness is not assumed; deployed rates use only an explicitly proved regime.
- Until a concrete PCS, CR, and shared-ROM game instantiate the controller, this is not a deployed
  succinct proof or security claim.

## Alternatives rejected

- One universal AIR/field: cannot preserve binary, odd-characteristic, and residue-ring semantics.
- A fourth bespoke WARP/PCS interface: repeats the same missing commitment/transcript object.
- Additive FRI as the per-turn accumulator: loses the stronger history/extraction structure.
- Shifted same-round root scoring: retains the adaptive increment/root-lag gap.

## Required evidence

- `Compiler.AuthenticatedColumnPlan`: typed roots-before-challenges executable controller.
- `Assurance.SemanticHistoryWARPAdditiveJoin`: exact dual-root/history/checkpoint join.
- A concrete Tower256 codec, commitment binding/CR proof, shared-ROM reduction, and sampled PCS
  decider before a deployment claim.
- Remote evidence records must name the exact commit and command and may claim only that check.

## Revisit trigger

Revisit if a straight-line knowledge-sound, hiding PCS with strictly simpler typed composition
subsumes both WARP link attribution and additive checkpoints in the required transparent/PQ model.

## Current source anchors

- `Assurance/SemanticHistoryAccumulator.lean`
- `Assurance/SemanticHistoryStraightlinePcs.lean`
- `Assurance/SemanticAdditiveFriCheckpoint.lean`
- `Compiler/AdditiveFriReceiptClause.lean`
- `Compiler/Logup256ReceiptClause.lean`

