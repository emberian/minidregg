/-
# Assurance.TwoRegimeQueryBudget — the FRI query wall, with the DECODING REGIME IN THE TYPE.

`ErrorBudget` prices the *algebraic* failure events and lands one number (55 bits
at BabyBear⁴), and every term in it divides by `|F|`: it is a **field-size** wall,
and a wider extension moves it. This file prices the **other** wall, the one a
wider extension does not move at all — the FRI **query phase** — and it makes the
thing our record got wrong impossible to say:

> **A soundness number is meaningless without its decoding regime, and the regime
> is not a footnote — it is part of the number's TYPE.**

## The three regimes, and why two of them are not the third

FRI's query-phase error is `(1 − θ)^q / 2^g`: `q` independent spot-checks, each
surviving with probability `1 − θ`, times the query grinding. `θ` is the *decoding
radius* the proximity-gap analysis is run at, and there are three answers in
circulation:

| regime | `θ` | `1 − θ` at rate `ρ` | status |
|---|---|---|---|
| **UDR** — unique decoding | `(1 − ρ)/2` | `(1 + ρ)/2` | **proven**, unconditional, list size 1 |
| **JBR** — Johnson bound   | `1 − √ρ`   | `√ρ`        | **idealised**: this is BCIKS20's `α = √ρ·(1 + 1/2m)` at `m → ∞`, an over-claim at every finite `m` |
| **CBR** — capacity        | `1 − ρ`    | `ρ`         | ⚑ **WITHDRAWN**: the conjecture beneath it is REFUTED |

`CBR`'s conjecture is refuted by Crites–Stewart (eprint 2025/2046) and Kambiré
(arXiv 2604.09724). The Ethereum Foundation's own calculator **deleted the
capacity regime outright** — `ethereum/soundcalc` commit `ffaeb81`, 2025-11-17,
*"Remove CBR (due to DG25 and CS25)"*; only UDR and JBR remain there.

**Our tree carries the capacity column anyway**, as
`Dregg2.Circuit.FriLedger.capacityBits = numQueries·logBlowup + powBits`
(breadstuffs `metatheory/Dregg2/Circuit/FriLedger.lean:204`), and it is the source
of the "conjectured 130" that has circulated in our summaries. `130` is
`19·6 + 16` at the deployed IR-v2 knobs — **it is the CBR reading, and CBR is the
withdrawn regime.** `ir2_the_conjectured_130_is_the_withdrawn_regime` below states
that identification as a theorem rather than as prose.

**And the ledger has no UDR column at all.** `johnsonBits` (JBR) and
`capacityBits` (CBR) are its only two, so the regime that is unconditionally
proven is absent from the object every shipped config is judged against.
`ir2_three_regimes` computes it for the deployed knobs: **34 bits.**

⚠ Narrowly and honestly: a unique-decoding query bound *does* exist elsewhere in
the tree — `Dregg2.Circuit.FriVerifierQuery.epsilon_query_deployed_query_term_lt`
proves `(9/16)^38 < 2^(−31)`, which is exactly this column at `δ = 7/16` (the UDR
radius at `logBlowup = 3`) and `q = 38`. It is **one-sided**, it **omits the
grinding bits entirely**, and it is stated only for the `lb = 3, q = 38` shape,
never for the deployed IR-v2 `lb = 6, q = 19`. `prodV1_udr_agrees_with_metatheory`
below checks our formula against it: `31 + 16 = 47`, which is what
`prodV1_three_regimes` reports. Two independently written definitions, same
number — the existing bound is this file's UDR column minus its `powBits`.

## What the type does

`QErr r` is indexed by the regime. `QErr .UDR` and `QErr .JBR` are *different
types*: there is no `+`, no `min`, no `≤` relating them, so a UDR number and a JBR
number cannot be summed into a budget or compared into a "min over components"
without an explicit, visible regime change. That is the defect this file exists to
make unsayable — our own record compared `130` (CBR), `73` (JBR) and `51`
(`commitBits`) in one breath, and the memory index still does.

## Two-sided, always

`QErr.Bits e k` is `e ≤ 2^(−k) ∧ 2^(−(k+1)) < e`: the promise AND the refutation
of the next bit. A one-sided `≤` is satisfied by every loose bound there is
(`error ≤ 2^0` holds of everything), so `bits_unique` proves the two-sided form
pins `k` — at most one `k` can satisfy it. This generalises the
`deployedBudget_secure` / `deployedBudget_ceiling` pair of `Assurance.ErrorBudget`
into one predicate that carries its own non-vacuity.

## Why everything here is exact rational arithmetic, and there is no `native_decide`

JBR's `1 − θ = √ρ` is irrational at odd `logBlowup`, which is why the Ethereum
calculator and its Lean companion carry certified `√·` *enclosures*. For the query
column specifically the enclosure is unnecessary: the error is a **product of `q`
copies of `1 − θ`**, so its SQUARE is `((1 − θ)²)^q / 4^g`, and `(1 − θ)²` is
rational at all three regimes — `((1+ρ)/2)²`, `ρ`, `ρ²`. `QErr` therefore stores
the square, and `bits_iff_real` proves the squared statement is *equivalent* (not
merely conservative) to the two-sided statement about the genuine real-valued
error `Real.sqrt (…) ^ q / 2 ^ g`. Every cell below is closed by kernel `norm_num`
over ℚ. **No `native_decide`, no `sorry`, no `#guard`, no floats.**

## Scope, in the same sentence as the claim

This file prices **one column** — the query phase — at three regimes, and nothing
else. It is not a composed soundness number: BCIKS20's commit-phase term `ε_C`
(breadstuffs' `friCommitLedger`, which reads **51** at the deployed wrap) is a
separate addend that contains neither `numQueries` nor `powBits`, and ethSTARK
eq. (20) composes the two as a `min`. A `min` of a UDR query column against a
commit column derived at a different proximity parameter is exactly the
regime-mixing this file forbids; composing them correctly requires stating `ε_C`
at a matching `θ`, which is not done here and is not claimed.
-/
import Mathlib

namespace Minidregg.Assurance

/-! ## §1 The regime, and its epistemic status -/

/-- The decoding regime a FRI proximity analysis is run at. This is an *analysis*
parameter, not a prover or verifier parameter: the same shipped configuration has
a different soundness number at each of these, and choosing one is a claim about
which theorem you are standing on. -/
inductive Regime where
  /-- Unique decoding, `θ = (1 − ρ)/2`. List size 1; unconditional. -/
  | UDR
  /-- Johnson bound, `θ = 1 − √ρ`. List size > 1; BCIKS20 at `m → ∞`. -/
  | JBR
  /-- Capacity, `θ = 1 − ρ`. The conjecture beneath it is REFUTED. -/
  | CBR
  deriving DecidableEq, Repr, Inhabited

/-- What is actually known about a regime's decoding radius. Carried so that
`withdrawn_is_not_reportable` can be a theorem instead of a comment. -/
inductive RegimeStatus where
  /-- Holds unconditionally, for any code. -/
  | proven
  /-- Holds only in a limit the deployed protocol does not take. -/
  | idealised
  /-- The assumption beneath it has been refuted. -/
  | withdrawn
  deriving DecidableEq, Repr, Inhabited

/-- `UDR` is proven; `JBR` is the `m → ∞` idealisation of BCIKS20's
`α = √ρ·(1 + 1/2m)` and is an over-claim at every finite `m`; `CBR` is withdrawn
(Crites–Stewart eprint 2025/2046; Kambiré arXiv 2604.09724; and
`ethereum/soundcalc` deleted the regime in `ffaeb81`, 2025-11-17). -/
def Regime.status : Regime → RegimeStatus
  | .UDR => .proven
  | .JBR => .idealised
  | .CBR => .withdrawn

/-- A number may be reported as *the* soundness of a configuration only from a
regime that has not been withdrawn. -/
def Regime.Reportable (r : Regime) : Prop := r.status ≠ .withdrawn

theorem udr_reportable : Regime.UDR.Reportable := by
  unfold Regime.Reportable Regime.status; decide
theorem jbr_reportable : Regime.JBR.Reportable := by
  unfold Regime.Reportable Regime.status; decide

/-- ⚑ **The capacity regime is not reportable.** Anything read off `CBR` — the
`capacityBits` column, the "conjectured 130" — is a number from a withdrawn
analysis, and this is the statement that says so mechanically. -/
theorem cbr_not_reportable : ¬ Regime.CBR.Reportable := by
  unfold Regime.Reportable Regime.status; decide

/-! ## §2 The query-phase configuration and its regime-indexed error -/

/-- The three knobs the FRI query phase actually depends on. **There is no field
here, and that absence is the content of §6**: extension degree — the entire fix
for the LogUp/field-size wall — does not appear in this column at all. -/
structure FriQueryCfg where
  /-- Rate `ρ = 2^(−logBlowup)`. -/
  logBlowup : ℕ
  /-- Number of independent query spot-checks. -/
  numQueries : ℕ
  /-- Query-phase proof-of-work (grinding) bits. -/
  powBits : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The code rate `ρ = 2^(−logBlowup)`. -/
def FriQueryCfg.rate (c : FriQueryCfg) : ℚ := 1 / 2 ^ c.logBlowup

theorem FriQueryCfg.rate_pos (c : FriQueryCfg) : 0 < c.rate := by
  unfold FriQueryCfg.rate; positivity

/-- `(1 − θ_r)²`, the SQUARE of the per-query survival probability. Squaring is
what removes JBR's `√ρ`: all three branches are rational, so every cell in this
file is kernel arithmetic over ℚ. -/
def survivalSq : Regime → ℚ → ℚ
  | .UDR, ρ => ((1 + ρ) / 2) ^ 2
  | .JBR, ρ => ρ
  | .CBR, ρ => ρ ^ 2

theorem survivalSq_pos {ρ : ℚ} (hρ : 0 < ρ) (r : Regime) : 0 < survivalSq r ρ := by
  cases r <;> unfold survivalSq <;> positivity

/-- **The query-phase soundness error, carrying its regime IN THE TYPE.**

`QErr .UDR` and `QErr .JBR` are different types. There is no heterogeneous `+`,
`min` or `≤` between them, so a UDR number and a JBR number cannot be summed into
a budget or compared into a "total = min over components" without an explicit,
visible change of regime. `errSq` is the SQUARE of the error (see the header). -/
structure QErr (r : Regime) where
  /-- The square of the query-phase soundness error. -/
  errSq : ℚ
  deriving DecidableEq, Repr

/-- The query-phase error of `c`, analysed at regime `r`. -/
def queryErr (r : Regime) (c : FriQueryCfg) : QErr r :=
  ⟨survivalSq r c.rate ^ c.numQueries / 4 ^ c.powBits⟩

theorem queryErr_pos (r : Regime) (c : FriQueryCfg) : 0 < (queryErr r c).errSq := by
  have := survivalSq_pos c.rate_pos r
  unfold queryErr
  simp only
  positivity

/-! ## §3 Two-sided bits, and why one-sided is not enough -/

/-- **The two-sided bit count.** `e.Bits k` says the error is *exactly* `k` bits:
`e ≤ 2^(−k)` — the promise — **and** `2^(−(k+1)) < e` — the next bit refuted.

Stated on the square, where `2^(−k)` becomes `4^(−k)`; `bits_iff_real` proves this
is equivalent to the two-sided statement about the genuine real-valued error.

A one-sided `≤` carries no information about tightness: `error ≤ 2^0` is true of
every error there is, so a `≤`-only claim can be vacuously loose. `bits_unique`
shows the two-sided form cannot be. -/
def QErr.Bits {r : Regime} (e : QErr r) (k : ℕ) : Prop :=
  e.errSq ≤ 1 / 4 ^ k ∧ 1 / 4 ^ (k + 1) < e.errSq

/-- **A two-sided bound pins the number.** At most one `k` satisfies `e.Bits k`,
so a `Bits` claim is a *measurement*, not a bound that can be weakened at will.
This is the property a one-sided `≤` does not have, and it is the reason every
cell below is stated two-sided. -/
theorem bits_unique {r : Regime} {e : QErr r} {j k : ℕ}
    (hj : e.Bits j) (hk : e.Bits k) : j = k := by
  by_contra hne
  -- WLOG `j < k`; then `e ≤ 4^(−k) ≤ 4^(−(j+1)) < e`.
  rcases Nat.lt_or_ge j k with h | h
  · -- `1/4^(j+1) < e ≤ 1/4^k ≤ 1/4^(j+1)`
    have hle : (1 : ℚ) / 4 ^ k ≤ 1 / 4 ^ (j + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) h
    have := lt_of_lt_of_le (lt_of_lt_of_le hj.2 hk.1) hle
    exact absurd this (lt_irrefl _)
  · have hlt : k < j := by omega
    have hle : (1 : ℚ) / 4 ^ j ≤ 1 / 4 ^ (k + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) hlt
    have := lt_of_lt_of_le (lt_of_lt_of_le hk.2 hj.1) hle
    exact absurd this (lt_irrefl _)

/-! ### The bridge to the genuine real-valued error

Nothing above would mean anything if the square were a dodge. It is not: the
squared statement is *equivalent* — not merely conservative — to the two-sided
statement about the real error with its true, possibly irrational, `1 − θ`. -/

/-- The genuine query-phase error, with the true (possibly irrational) `1 − θ`:
`(1 − θ_r)^q / 2^g`. At JBR this is `(√ρ)^q / 2^g`; the whole point of `errSq` is
that this quantity's *square* is rational. -/
noncomputable def queryErrReal (r : Regime) (c : FriQueryCfg) : ℝ :=
  Real.sqrt ((survivalSq r c.rate : ℚ) : ℝ) ^ c.numQueries / 2 ^ c.powBits

theorem queryErrReal_nonneg (r : Regime) (c : FriQueryCfg) : 0 ≤ queryErrReal r c := by
  unfold queryErrReal; positivity

private theorem sq_le_sq_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 ≤ b ^ 2 ↔ a ≤ b := by
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

private theorem sq_lt_sq_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 < b ^ 2 ↔ a < b := by
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

private theorem four_pow_eq (k : ℕ) : ((4 : ℝ)) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- **The square is not a dodge.** The real-valued query error squares to exactly
the rational `errSq`, so every `norm_num` cell below is a statement about the
genuine quantity. -/
theorem queryErrReal_sq (r : Regime) (c : FriQueryCfg) :
    queryErrReal r c ^ 2 = ((queryErr r c).errSq : ℝ) := by
  have hs : (0 : ℝ) ≤ ((survivalSq r c.rate : ℚ) : ℝ) :=
    le_of_lt (by exact_mod_cast survivalSq_pos c.rate_pos r)
  unfold queryErrReal queryErr
  simp only
  rw [div_pow, ← pow_mul, mul_comm c.numQueries 2, pow_mul, Real.sq_sqrt hs,
    ← four_pow_eq]
  push_cast
  ring

/-- **The squared two-sided statement is EQUIVALENT to the real one.** `e.Bits k`
holds iff the genuine real-valued error is `≤ 2^(−k)` and `> 2^(−(k+1))`. -/
theorem bits_iff_real (r : Regime) (c : FriQueryCfg) (k : ℕ) :
    (queryErr r c).Bits k ↔
      queryErrReal r c ≤ 1 / 2 ^ k ∧ 1 / 2 ^ (k + 1) < queryErrReal r c := by
  have hE := queryErrReal_nonneg r c
  have hsq := queryErrReal_sq r c
  have h1 : ∀ m : ℕ, ((1 : ℝ) / 2 ^ m) ^ 2 = 1 / 4 ^ m := by
    intro m; rw [div_pow, one_pow, ← four_pow_eq]
  -- the ℚ→ℝ image of the rational threshold `1/4^m`
  have hQ : ∀ m : ℕ, (((1 : ℚ) / 4 ^ m : ℚ) : ℝ) = 1 / 4 ^ m := by
    intro m; push_cast; ring
  constructor
  · rintro ⟨hle, hlt⟩
    refine ⟨?_, ?_⟩
    · rw [← sq_le_sq_iff hE (by positivity), hsq, h1]
      calc ((queryErr r c).errSq : ℝ) ≤ (((1 : ℚ) / 4 ^ k : ℚ) : ℝ) := by exact_mod_cast hle
        _ = 1 / 4 ^ k := hQ k
    · rw [← sq_lt_sq_iff (by positivity) hE, hsq, h1]
      calc (1 : ℝ) / 4 ^ (k + 1) = (((1 : ℚ) / 4 ^ (k + 1) : ℚ) : ℝ) := (hQ (k + 1)).symm
        _ < ((queryErr r c).errSq : ℝ) := by exact_mod_cast hlt
  · rintro ⟨hle, hlt⟩
    have hle' : queryErrReal r c ^ 2 ≤ ((1 : ℝ) / 2 ^ k) ^ 2 :=
      (sq_le_sq_iff hE (by positivity)).mpr hle
    have hlt' : ((1 : ℝ) / 2 ^ (k + 1)) ^ 2 < queryErrReal r c ^ 2 :=
      (sq_lt_sq_iff (by positivity) hE).mpr hlt
    rw [hsq, h1] at hle' hlt'
    rw [← hQ k] at hle'
    rw [← hQ (k + 1)] at hlt'
    exact ⟨by exact_mod_cast hle', by exact_mod_cast hlt'⟩

/-! ## §4 The deployed configurations, read off the Rust constants

Every knob below is transcribed from a named constant in the breadstuffs tree; the
file:line is in each docstring. Nothing here is estimated. -/

/-- **IR-v2 descriptor batch** — the app/leaf mint that a light client verifies.
`circuit/src/descriptor_ir2.rs:7244` (`IR2_FRI_LOG_BLOWUP = 6`), `:7247`
(`IR2_FRI_NUM_QUERIES = 19`), `:7248` (`IR2_FRI_QUERY_POW_BITS = 16`). -/
def ir2 : FriQueryCfg := { logBlowup := 6, numQueries := 19, powBits := 16 }

/-- **Recursion tree default** — the weakest shipped config on the query column.
`recursion-verify/src/config.rs:51` (`RECURSION_FRI_LOG_BLOWUP = 3`), `:53`
(`RECURSION_FRI_NUM_QUERIES = 38`), `:58` (`RECURSION_FRI_QUERY_POW_BITS = 14`). -/
def recursionCfg : FriQueryCfg := { logBlowup := 3, numQueries := 38, powBits := 14 }

/-- **v1 production uni-STARK.** `circuit/src/plonky3_prover.rs:68, :71, :72`
(`PROD_FRI_LOG_BLOWUP = 3`, `PROD_FRI_NUM_QUERIES = 38`,
`PROD_FRI_QUERY_POW_BITS = 16`). The ZK lane (`circuit/src/stark_zk.rs:58-73`) and
the BN254 outer shrink (`circuit-prove/src/dregg_outer_config.rs:134-138`) carry
the same three values. -/
def prodV1 : FriQueryCfg := { logBlowup := 3, numQueries := 38, powBits := 16 }

/-- **zkDTVM v0.8.0 core** — the published recipe for proven-128 on a 31-bit
field: rate `1/2`, 261 queries, 20 grinding bits, and `explicit_regime = "unique"`
(i.e. UDR). Reproduced here as the calibration cell: `zkdtvm_core_is_128` gets
`128` out of *our* formula, independently. -/
def zkdtvmCore : FriQueryCfg := { logBlowup := 1, numQueries := 261, powBits := 20 }

/-! ## §5 THE CELLS — every one two-sided, every one at a named regime -/

/-- ⚑ **THE TEETH: one configuration, three regimes, ninety-six bits apart.**

The deployed IR-v2 query column reads **34** bits at UDR, **73** at JBR and
**130** at CBR. These are the same `q = 19`, `lb = 6`, `pow = 16` — nothing about
the shipped artifact differs between the three. A number quoted without its regime
is not imprecise; it is a choice of one of these three, made silently.

`73` is `Dregg2.Circuit.FriLedger.johnsonBits`; `130` is its `capacityBits`. **The
`34` is not in the ledger**, which has no UDR column at all — so the only
unconditionally proven reading of the *deployed* query phase did not exist before
this theorem. (The tree's one existing UDR query bound covers a different shape;
see the header, and `prodV1_udr_agrees_with_metatheory` for the cross-check.) -/
theorem ir2_three_regimes :
    (queryErr .UDR ir2).Bits 34
      ∧ (queryErr .JBR ir2).Bits 73
      ∧ (queryErr .CBR ir2).Bits 130 := by
  refine ⟨⟨by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2],
          by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2]⟩,
         ⟨by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2],
          by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2]⟩,
         ⟨by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2],
          by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2]⟩⟩

/-- ⚑ **The "conjectured 130" IS the withdrawn regime.** The number that has
circulated in our summaries as the optimistic end of the pair
"conjectured 130 / proven 51–73" is exactly `(queryErr .CBR ir2)`, and `.CBR` is
`.withdrawn`. It is not an optimistic bound; it is a bound from an analysis whose
premise has been refuted, and the Ethereum Foundation deleted the regime that
produces it from its own calculator on 2025-11-17.

The right reading of that pair, with the regimes restored, is
**UDR 34 / JBR 73 / (withdrawn) 130** — and `130 − 73 = 57` of the apparent
headroom is the withdrawal, not a knob. -/
theorem ir2_the_conjectured_130_is_the_withdrawn_regime :
    (queryErr .CBR ir2).Bits 130 ∧ Regime.CBR.status = .withdrawn := by
  refine ⟨⟨by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2],
           by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2]⟩, by decide⟩

/-- ⚑ **Only the withdrawn regime clears 128.** At the deployed IR-v2 knobs
neither reportable regime reaches even half of 128 bits on this column: UDR is
`34` and JBR is `73`, and `128` is reached only at `CBR`. The `128` that appears
as a floor in the shipped gate (`CAPACITY_DRIFT_MARGIN_BITS`,
`circuit-prove/tests/fri_params_soundness_budget.rs:205`) is a reading of that
same withdrawn column — the file calls it a drift canary, and this theorem is why
it must stay one. -/
theorem ir2_only_the_withdrawn_regime_clears_128 :
    ¬ (queryErr .UDR ir2).errSq ≤ 1 / 4 ^ 128
      ∧ ¬ (queryErr .JBR ir2).errSq ≤ 1 / 4 ^ 128
      ∧ (queryErr .CBR ir2).errSq ≤ 1 / 4 ^ 128 := by
  refine ⟨by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2],
          by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2],
          by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2]⟩

/-- The recursion tree default, at all three regimes: **45 / 71 / 128**. Its `128`
at CBR is exactly the shipped gate's `CAPACITY_DRIFT_MARGIN_BITS`, and its `71` at
JBR is exactly the shipped gate's `JOHNSON_FLOOR_BITS` — both floors are set by
this config with zero headroom, which the gate says of itself. Its proven-regime
reading, `45`, is again a number that did not previously exist. -/
theorem recursion_three_regimes :
    (queryErr .UDR recursionCfg).Bits 45
      ∧ (queryErr .JBR recursionCfg).Bits 71
      ∧ (queryErr .CBR recursionCfg).Bits 128 := by
  refine ⟨⟨by norm_num [queryErr, survivalSq, FriQueryCfg.rate, recursionCfg],
           by norm_num [queryErr, survivalSq, FriQueryCfg.rate, recursionCfg]⟩,
          ⟨by norm_num [queryErr, survivalSq, FriQueryCfg.rate, recursionCfg],
           by norm_num [queryErr, survivalSq, FriQueryCfg.rate, recursionCfg]⟩,
          ⟨by norm_num [queryErr, survivalSq, FriQueryCfg.rate, recursionCfg],
           by norm_num [queryErr, survivalSq, FriQueryCfg.rate, recursionCfg]⟩⟩

/-- The v1 production / ZK / BN254-outer knobs: **47 / 73 / 130**. -/
theorem prodV1_three_regimes :
    (queryErr .UDR prodV1).Bits 47
      ∧ (queryErr .JBR prodV1).Bits 73
      ∧ (queryErr .CBR prodV1).Bits 130 := by
  refine ⟨⟨by norm_num [queryErr, survivalSq, FriQueryCfg.rate, prodV1],
           by norm_num [queryErr, survivalSq, FriQueryCfg.rate, prodV1]⟩,
          ⟨by norm_num [queryErr, survivalSq, FriQueryCfg.rate, prodV1],
           by norm_num [queryErr, survivalSq, FriQueryCfg.rate, prodV1]⟩,
          ⟨by norm_num [queryErr, survivalSq, FriQueryCfg.rate, prodV1],
           by norm_num [queryErr, survivalSq, FriQueryCfg.rate, prodV1]⟩⟩

/-- **Cross-check against an independently written in-tree bound.**
`Dregg2.Circuit.FriVerifierQuery.epsilon_query_deployed_query_term_lt` proves
`(9/16)^38 < 2^(−31)` — the same column at the same knobs (`δ = 7/16` is the UDR
radius at `logBlowup = 3`; `q = 38`), written from a different definition, with the
`powBits` left out. Our `survivalSq .UDR` at `ρ = 1/8` is `(9/16)²` — it is the
square of `1 − θ`, and `9/16` is exactly that `1 − θ` — so the two definitions
meet, and `prodV1_three_regimes` reports `47 = 31 + 16`: the difference is
precisely the 16 grinding bits the older bound does not carry.

Stated here two-sided, which the older bound is not: `(9/16)^38` is also strictly
above `2^(−32)`, so `31` is tight and not a loose `<`. -/
theorem prodV1_udr_agrees_with_metatheory :
    survivalSq .UDR prodV1.rate = (9 / 16) ^ 2
      ∧ (9 / 16 : ℚ) ^ 38 < 1 / 2 ^ 31
      ∧ 1 / 2 ^ 32 < (9 / 16 : ℚ) ^ 38 := by
  refine ⟨by norm_num [survivalSq, FriQueryCfg.rate, prodV1], by norm_num, by norm_num⟩

/-- ⚑ **THE CALIBRATION CELL — zkDTVM's published proven-128, reproduced.**

zkDTVM v0.8.0 reaches 128 bits on a 31-bit field with rate `1/2`, **261** queries,
**20** grinding bits, at `explicit_regime = "unique"`. Our formula, written from
the definition of the unique-decoding radius and evaluated in exact rationals,
gets `128` — the same number, at the same regime, from an independent
implementation.

The instructive part is the JBR column: at `ρ = 1/2` the Johnson reading is `150`,
**22 bits above** the number zkDTVM actually publishes. zkDTVM does not claim the
150. Choosing the conservative regime and then buying the queries to pay for it is
the whole of its recipe, and it is the opposite of what our ledger does. -/
theorem zkdtvm_core_is_128 :
    (queryErr .UDR zkdtvmCore).Bits 128 ∧ (queryErr .JBR zkdtvmCore).Bits 150 := by
  -- `norm_num`'s power extension declines exponents above 255, so the 261 queries
  -- are split as `3 · 87` first. Nothing else changes; this is purely a tactic
  -- accommodation, and the statement is the unsplit one.
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [queryErr, survivalSq, FriQueryCfg.rate, zkdtvmCore,
      show (261 : ℕ) = 3 * 87 from rfl, pow_mul] <;>
    norm_num

/-- ⚑ **Nineteen queries cannot reach 128 at any regime that is still standing.**

At the deployed rate `ρ = 2^(−6)` a single query is worth `1 − log₂(1 + ρ) ≈ 0.978`
bits at UDR and `logBlowup/2 = 3` bits at JBR. Nineteen of them plus 16 grinding
bits is `34` and `73`. The gap to 128 is not a rounding: reaching it on this column
requires more queries or more grinding — the levers zkDTVM pulls — and **no
extension-degree change touches it at all** (§6). -/
theorem ir2_cannot_reach_128_at_a_reportable_regime :
    ∀ r : Regime, r.Reportable → ¬ (queryErr r ir2).errSq ≤ 1 / 4 ^ 128 := by
  intro r hr
  cases r
  · exact by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2]
  · exact by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2]
  · exact absurd rfl hr

/-! ### The tooth with a live edge: `numQueries` is prover-supplied under recursion

`q` is the only knob in this column, and the in-circuit recursion verifier **reads
it from the child's proof**:

```rust
// plonky3-recursion, recursion/src/pcs/fri/verifier.rs:1378
let num_queries = fri_proof_targets.query_proofs.len();
```

`FriVerifierParams` (`recursion/src/pcs/fri/params.rs:8-23`) has no `num_queries`
field at all, so there is nothing to pin it against; the only checks inside
`verify_fri_circuit` compare the proof with quantities derived from the same
proof. The *native* verifier does pin it
(`vendor/plonky3-fri-82cfad73/src/verifier.rs:241-243`,
`QueryProofCountMismatch`). This is recorded in-tree at
`circuit/src/descriptor_ir2.rs:7200-7204` as *"masked today only because every
child runs 19 queries."* -/

/-- The IR-v2 knobs with a child that minted one query instead of nineteen —
which the in-circuit recursion verifier accepts, because it takes the count from
the proof. -/
def ir2ForgedOneQuery : FriQueryCfg := { ir2 with numQueries := 1 }

/-- ⚑ **What the unpinned `numQueries` is worth, priced.** A child proof carrying
one query proof instead of nineteen collapses the query column to **16 bits at
UDR and 19 at JBR** — essentially the grinding floor, since the queries were the
only thing above it. Against the deployed `34 / 73` that is a loss of 18 and 54
bits, available to a prover that simply mints fewer queries.

This is the sharpest difference between the two 100-bit walls and it is not about
size: the LogUp/field wall is *structural* — the extension degree is compiled into
the verifier and a prover cannot move it — while the query wall is **carried in
the proof** at every recursion layer. A wall a prover can lower is not a wall. -/
theorem unpinned_query_count_collapses_the_column :
    (queryErr .UDR ir2ForgedOneQuery).Bits 16
      ∧ (queryErr .JBR ir2ForgedOneQuery).Bits 19 := by
  refine ⟨⟨by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2ForgedOneQuery, ir2],
           by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2ForgedOneQuery, ir2]⟩,
          ⟨by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2ForgedOneQuery, ir2],
           by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2ForgedOneQuery, ir2]⟩⟩

/-! ## §6 The OTHER hundred-bit wall — and why it needs a different fix

LogUp's fingerprint bound is `ε ≤ K·H·R/|F|`: `K` lookup arguments over `H` rows
with column-aggregation factor `R`, against the challenge field. It is a
Schwartz–Zippel root count, **not** a decoding-radius bound — there is no `θ` in
it, hence no regime to tag, and `logupErr` below correctly takes no `Regime`.

That is the whole asymmetry:

* the **LogUp wall is field-size-bound** — `|F|` is in the denominator, so the
  extension degree moves it, and Ext4 → Ext5 is worth `⌊log₂ p⌋ = 30` bits;
* the **FRI query wall is query-count-bound** — `queryErr` has no `|F|` in it at
  all, so the extension degree moves it by exactly nothing.

A system can therefore be at 100 bits on one wall and 34 on the other, and a
single headline number will report whichever it happened to compute. -/

/-- LogUp's fingerprint parameters. -/
structure LogUpCfg where
  /-- `K` — number of lookup arguments. -/
  numLookups : ℕ
  /-- `H` — total rows (`rowsT + rowsL`). -/
  rows : ℕ
  /-- `R` — column-aggregation factor (the tuple arity, univariate path). -/
  colFactor : ℕ
  /-- Lookup-phase grinding bits. -/
  grindBits : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- `ε ≤ K·H·R / (|F| · 2^grind)`. **No `Regime` argument, deliberately**: this is
a root count, valid at unique decoding, at the Johnson bound and at capacity
alike. `logup_carries_no_regime` states that as a theorem. -/
def logupErr (fieldCard : ℕ) (c : LogUpCfg) : ℚ :=
  (c.numLookups * c.rows * c.colFactor : ℚ) / (fieldCard : ℚ) / 2 ^ c.grindBits

/-- Two-sided bits for a LogUp cell (on the value, not its square — there is no
irrational here to remove). -/
def LogUpBits (fieldCard : ℕ) (c : LogUpCfg) (k : ℕ) : Prop :=
  logupErr fieldCard c ≤ 1 / 2 ^ k ∧ 1 / 2 ^ (k + 1) < logupErr fieldCard c

/-- **The LogUp wall carries no regime, and that is a statement about the bound,
not an omission.** `logupErr` is a function of the field and the table shape only:
the same value is the correct bound whichever decoding regime the FRI layer is
analysed at. Two walls, two kinds of quantity — which is exactly why one number
cannot describe both. -/
theorem logup_carries_no_regime (F : ℕ) (c : LogUpCfg) (r r' : Regime) :
    (fun _ : Regime => logupErr F c) r = (fun _ : Regime => logupErr F c) r' := rfl

/-- The BabyBear prime `p = 2^31 − 2^27 + 1`, the deployed base field. -/
def babyBearP : ℕ := 2013265921

/-- The deployed challenge field `BabyBear⁴`, `|F| = p⁴ ≈ 2^123.63`. Every shipped
config uses `BinomialExtensionField<BabyBear, 4>`
(`recursion-verify/src/config.rs:38,101`; `circuit/src/plonky3_prover.rs:60,84`). -/
def babyBear4 : ℕ := babyBearP ^ 4

/-- The Ext5 candidate. -/
def babyBear5 : ℕ := babyBearP ^ 5

/-- ⚑ **The LogUp headroom at BabyBear⁴, exactly.** `|F| = p⁴` sits between
`2^123` and `2^124`, so a LogUp cell with no grinding clears 100 bits iff
`K·H·R ≤ ⌊p⁴/2^100⌋ = 12960000 < 2^23.63`. The deployed row ceiling is `2^21`
(BabyBear two-adicity 27 minus `log_blowup` 6;
`circuit-prove/src/collaborative_basefold.rs:59`), which leaves `K·R ≤ 6` before
the wall binds. That is a very small budget for a batch with ten committed tables. -/
theorem babyBear4_logup_headroom_at_100 :
    2 ^ 123 < babyBear4 ∧ babyBear4 < 2 ^ 124 ∧ babyBear4 / 2 ^ 100 = 12960000 := by
  refine ⟨by norm_num [babyBear4, babyBearP], by norm_num [babyBear4, babyBearP],
          by norm_num [babyBear4, babyBearP]⟩

/-- A LogUp cell at the deployed *caps*: one lookup argument over the exact-public
table at its maximum admitted shape — `MAX_EXACT_PUBLIC_ROWS = 1 << 21`
(`circuit/src/descriptor_ir2.rs:590`) and `MAX_EXACT_PUBLIC_ARITY = 97` (`:616`),
no lookup grinding.

⚠ **This is the admitted CAP, not a measurement.** No measured `(K, H, R)` for the
shipped IR-v2 batch exists in the tree, and none is invented here; the cap is what
the descriptor validator (`descriptor_ir2.rs:2404-2410`) will accept. -/
def deployedLogUpCap : LogUpCfg :=
  { numLookups := 1, rows := 2 ^ 21, colFactor := 97, grindBits := 0 }

/-- ⚑ **THE OTHER WALL, PRICED — and at BabyBear⁴ it is already below 100.**

At the admitted caps the LogUp cell reads **96 bits** at BabyBear⁴ and **126** at
BabyBear⁵. Two things follow, and they are the two halves of the grey-literature
finding:

1. **Ext5 is worth 30 bits here** — `96 → 126` — because `|F|` is in the
   denominator. This is the field-size wall and the extension degree is its fix.
2. **Ext5 is worth zero bits on the query column.** `ir2_three_regimes` reads
   `34 / 73 / 130` and would read `34 / 73 / 130` at any extension degree, because
   `queryErr` has no field in it.

Nothing on a degree-4 31-bit field reaches 128 — and the reason is not one wall
but two, with disjoint fixes. -/
theorem the_two_walls_move_on_different_levers :
    LogUpBits babyBear4 deployedLogUpCap 96
      ∧ LogUpBits babyBear5 deployedLogUpCap 126
      ∧ (queryErr .JBR ir2).Bits 73 := by
  refine ⟨⟨by norm_num [logupErr, deployedLogUpCap, babyBear4, babyBearP],
           by norm_num [logupErr, deployedLogUpCap, babyBear4, babyBearP]⟩,
          ⟨by norm_num [logupErr, deployedLogUpCap, babyBear5, babyBearP],
           by norm_num [logupErr, deployedLogUpCap, babyBear5, babyBearP]⟩,
          ⟨by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2],
           by norm_num [queryErr, survivalSq, FriQueryCfg.rate, ir2]⟩⟩

/-! ## §7 Axiom footprint

Kernel-checked throughout: the three standard axioms and nothing else. In
particular **no `Lean.ofReduceBool`** — no cell in this file goes through the
compiler, because the squaring trick of §2 keeps every one of them inside exact
rational arithmetic that `norm_num` closes in the kernel. -/

/-- info: 'Minidregg.Assurance.bits_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bits_unique
/-- info: 'Minidregg.Assurance.bits_iff_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bits_iff_real
/-- info: 'Minidregg.Assurance.queryErrReal_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms queryErrReal_sq
/-- info: 'Minidregg.Assurance.ir2_three_regimes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ir2_three_regimes
/-- info: 'Minidregg.Assurance.ir2_the_conjectured_130_is_the_withdrawn_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ir2_the_conjectured_130_is_the_withdrawn_regime
/-- info: 'Minidregg.Assurance.zkdtvm_core_is_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zkdtvm_core_is_128
/-- info: 'Minidregg.Assurance.unpinned_query_count_collapses_the_column' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unpinned_query_count_collapses_the_column
/-- info: 'Minidregg.Assurance.the_two_walls_move_on_different_levers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms the_two_walls_move_on_different_levers
/-- info: 'Minidregg.Assurance.prodV1_udr_agrees_with_metatheory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prodV1_udr_agrees_with_metatheory

end Minidregg.Assurance
