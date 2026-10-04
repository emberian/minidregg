# D-0006 — the un-fixed Polishchuk–Spielman floor was false

- Status: accepted (a refutation; nothing to choose)
- Date: 2026-10-04

## The wound

`Selvage/ProximityGapUDTight.lean` reached the full unique-decoding radius `(1 − ρ)/2` by the
BCIKS Berlekamp–Welch route and carried its one unproved step `[PROXGAP-BW-ps]` as a named
`Prop`, `Minidregg.Selvage.PolishchukSpielman F`:

```
∀ A B SX SZ aX aZ bX bZ,
  deg_X A ≤ aX → deg_Z A ≤ aZ → deg_X B ≤ bX → deg_Z B ≤ bZ →
  (∀ x ∈ SX, A(x, Z) ∣ B(x, Z)) → (∀ z ∈ SZ, A(X, z) ∣ B(X, z)) →
  aX + bX < |SX| → aZ + bZ < |SZ| → bX·|SZ| + bZ·|SX| < |SX|·|SZ| → A ∣ B
```

That is the [Spi95] Lemma 4.2.18 / BCIKS 2020/654 rev.1 shape. The statement is false, not
only its original proof. `Selvage/PolishchukSpielmanRefutation.lean` proves
`polishchukSpielman_unfixed_false`: over every field with two distinct nonzero elements,

- `A = 1 + X·Z`, `B = X − (x₁ + x₂) − x₁x₂·Z` (all four degrees `1`);
- `S_X = {0, x₁, x₂}`, `S_Z = {0, −x₁⁻¹, −x₂⁻¹}`;
- columns: `A(0, Z) = 1`, `B(x₁, Z) = −x₂·A(x₁, Z)`, `B(x₂, Z) = −x₁·A(x₂, Z)`;
- rows: `A(X, 0) = 1`, `B(X, −x₁⁻¹) = −x₁·A(X, −x₁⁻¹)`, and the same at `−x₂⁻¹`;
- counts: `1 + 1 < 3`, `1 + 1 < 3`, `3 + 3 < 9`;
- `A ∤ B`: the outer leading coefficients are `Z` and `1`, and `Z` is not a unit.

At `F₅` (`x₁ = 1`, `x₂ = 2`) this is `A = 1 + XZ`, `B = X + 2 + 3Z`, `S_X = {0,1,2}`,
`S_Z = {0,4,2}` (`polishchukSpielman_unfixed_false_F5`). The two lines through the origin
are where `A` degenerates to a unit, so plain divisibility on them costs nothing.

## What the fix is

The corrected statement (BCIKS rev.3 Appendix D; the fix due to Ronald Cramer, after
Cramer–Nardi's diagnosis; cf. [Bég19]) requires every per-line QUOTIENT to have degree at
most `b − a` in the line variable. On the column `x = 0` above, the only quotient is
`B(0, Z)`, of `Z`-degree `1 > b_Z − a_Z = 0`, so the fixed statement refuses the instance
(`counterexample_violates_cramer`). The fixed lemma is proved in breadstuffs
(`metatheory/Dregg2/ForMathlib/PolishchukSpielman.lean`, Mathlib-only, same toolchain).

## What was deleted, and why nothing else moves

Deleted: the def; the full-band core `correlatedAgreement_of_close_card_full`; the heads
`rs_proximityGap_UD_full`, `reedSolomonCode_isProximityGenerator_UD_full`,
`hasMutualCorrelatedAgreement_UD_full`, `foldDistancePreserving_UD_full`; the keystones
`ps_premises_inhabited` and `good_line_CA_fullBand`; the ledger pin and allowlist entry.
Every one of them was conditioned on the false `Prop`, so each was true of nothing at every
field the route is used at. A search of the whole tree found no other Lean consumer (only
`Selvage.lean` imports the file; `HalfThresholdFri*.lean` named the heads in comments).
The proved `(1 − ρ)/3` band (`Selvage/ProximityGapUD.lean`) is untouched and is still what
every deployed consumer uses. No re-emit, no re-genesis: Selvage is research, nothing at
admission reads it.

## Why every instrument missed it

- `#assert_axioms` is blind to a false premise.
- `ps_premises_inhabited` showed the premises satisfiable at `A = 1`, where the conclusion is
  trivial. Satisfiable-by-a-toy says nothing about truth.
- `scripts/HypothesisLedger.lean` marks a family REFUTED only on a GENERAL refutation
  (`∀ params, ¬ D params` with no hypothesis). This floor is false only at fields with at
  least three elements, so its refutation is conditional and the instance refutation at `F₅`
  is a `ref` pole, not a REFUTED status: the row would have read OPEN, never VACUOUS. A
  floor false at every field anyone uses still reads OPEN to that instrument.

## Rule

A named hypothesis gets a refutation attempt at its own consumers' field before it gets a
satisfiability witness.
