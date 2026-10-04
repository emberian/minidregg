/-
# Bfv.NoWrap — silent-failure class (C): the plaintext-modulus wrap, made RED.

**The failure this module kills:** the fold homomorphically adds ≤ N per-order quantity increments
into a bucket. The bucket lives in `Z_t`. If the accumulated PLAINTEXT sum reaches `t`, it WRAPS —
the bucket silently reads `sum − t`, the crossing mis-clears, and NOTHING errors anywhere: not the
FHE library, not decrypt, not the market logic. A wrapped bucket is a perfectly well-formed
ciphertext of the wrong number. The ONLY defense is an ingest-time cap `N·qmax < t`, and the only
honest form of that cap is a THEOREM about what it guarantees plus a PIN of the real numbers.

## What is proved

  1. **`fold_sum_no_wrap`** (the general gate) — for any list of quantities each `≤ qmax`, with at
     most `N` of them, if `N·qmax < t` then the true sum is `< t`: the fold's `Z_t` readout equals
     the integer sum, no wrap. This is the theorem the ingest cap enforces.
  2. **`wrap_misclears`** (what the wrap DOES — the mis-clear, named) — a sum in `[t, 2t)` reads
     back as `sum − t ≠ sum`. The wrap is not an error state; it is a WRONG NUMBER.
  3. **THE HONEST N BOUND for u16 quantities, stated plainly:** with full-range u16 quantities
     (`qmax = 65535`) and the deployed `t = 1032193`, the capacity is **N = 15 orders per bucket.
     FIFTEEN.** `u16_bucket_capacity` proves 15 is safe; `sixteen_can_wrap` proves 16 is NOT — a
     16-order all-max book truly holds 1,048,560 units but READS as 16,367 (`decide`-pinned, both
     polarities). The production cap must therefore either (a) cap orders-per-bucket at 15 for
     raw u16, or (b) cap `qmax` lower (e.g. `qmax ≤ 2^12 = 4096` gives capacity `N = 251`,
     `u12_bucket_capacity`). A cap that is not `decide`-pinned against these numbers is a comment.

## What is NOT claimed

  * Nothing here says the DEPLOYED Rust ingest enforces the cap — that is the Rust-side guard this
    theorem is the spec for (the Lean-emitted `N_max·q_max < t` constant is the deliverable the
    memo names). This module makes the cap's correctness a theorem; wiring it is named work.
  * The wrap bound is about the PLAINTEXT sum. Noise wrap (phase overflow) is class (A) —
    `Bfv.Noise` / `Bfv.Fold`.

Pure. No axioms beyond the kernel triple.

**Port provenance (Mini, 2026-10-04).** Copied from breadstuffs `metatheory/Bfv/NoWrap.lean`
(sha256 `3cd3bdf36a49c21e1de2f9f6303183593209c93d1c443942bf10aa78363bbc72`), renamespaced `Bfv` → `Minidregg.Theory.Bfv`; statements and proofs
unchanged; Bread's `#assert_all_clean` lists became Mini's `#print axioms` pins, recorded
against Bread's own axiom sets in `docs/BREAD-PORTS.md`. Mathlib-only imports.
-/
import Mathlib.Algebra.Order.BigOperators.Group.List
import Theory.BfvParams

namespace Minidregg.Theory.Bfv

/-! ## 1. The general no-wrap gate. -/

/-- **The no-wrap gate (class C killed):** at most `N` quantities, each `≤ qmax`, with the cap
`N·qmax < t` ⇒ the true accumulated sum stays strictly below the plaintext modulus, so the
bucket's `Z_t` readout IS the true sum — no silent wrap, no mis-clear. -/
theorem fold_sum_no_wrap (qs : List ℕ) (qmax N t : ℕ)
    (h_each : ∀ q ∈ qs, q ≤ qmax) (h_len : qs.length ≤ N) (h_cap : N * qmax < t) :
    qs.sum < t := by
  have h1 : qs.sum ≤ qs.length * qmax := by
    simpa [Nat.nsmul_eq_mul] using List.sum_le_card_nsmul qs qmax h_each
  have h2 : qs.length * qmax ≤ N * qmax := Nat.mul_le_mul_right _ h_len
  omega

/-- The gate is exactly what makes the modular readout faithful: under the same hypotheses, the
bucket's `Z_t` representative (`sum % t`) equals the integer sum. -/
theorem fold_readout_faithful (qs : List ℕ) (qmax N t : ℕ)
    (h_each : ∀ q ∈ qs, q ≤ qmax) (h_len : qs.length ≤ N) (h_cap : N * qmax < t) :
    qs.sum % t = qs.sum :=
  Nat.mod_eq_of_lt (fold_sum_no_wrap qs qmax N t h_each h_len h_cap)

/-! ## 2. What the wrap DOES — the mis-clear, named. -/

/-- **The silent mis-clear:** a sum that reaches `[t, 2t)` reads back as `sum − t`, which is a
DIFFERENT number — and nothing errors. This is why the cap must be enforced at ingest: past the
boundary the system keeps running, on wrong values. -/
theorem wrap_misclears (s t : ℕ) (h1 : t ≤ s) (h2 : s < 2 * t) :
    s % t = s - t ∧ s % t ≠ s := by
  have hmod : s % t = (s - t) % t := Nat.mod_eq_sub_mod h1
  have hlt : s - t < t := by omega
  rw [hmod, Nat.mod_eq_of_lt hlt]
  omega

/-! ## 3. The deployed numbers — the honest N bound, both polarities, `decide`-pinned. -/

/-- **The honest u16 capacity is FIFTEEN.** With full-range u16 quantities (`qmax = 65535`) and
the deployed `t = 1032193`: at most 15 orders per bucket is provably wrap-free. -/
theorem u16_bucket_capacity (qs : List ℕ)
    (h_each : ∀ q ∈ qs, q ≤ 65535) (h_len : qs.length ≤ 15) :
    qs.sum < fheRs4096.t :=
  fold_sum_no_wrap qs 65535 15 _ h_each h_len (by decide)

/-- **Sixteen full-range u16 orders CAN wrap — the bound is tight.** The all-max 16-order book
truly holds `16·65535 = 1,048,560` units, which is `≥ t`: the cap arithmetic fails at 16. -/
theorem sixteen_exceeds_t : ¬ (16 * 65535 < fheRs4096.t) := by decide

/-- **The concrete mis-clear witness:** that 16-order all-max bucket READS as `16367` — a
well-formed, error-free, WRONG number (`1,048,560 mod 1,032,193 = 16,367`). -/
theorem sixteen_misclears :
    (List.replicate 16 65535).sum = 1048560 ∧
    1048560 % fheRs4096.t = 16367 ∧ (16367 : ℕ) ≠ 1048560 := by decide

/-- The practical alternative cap: quantities pre-bounded to 12 bits (`qmax = 4095`) buy a
capacity of `N = 252` orders per bucket (`252·4095 = 1,031,940 < t`). -/
theorem u12_bucket_capacity (qs : List ℕ)
    (h_each : ∀ q ∈ qs, q ≤ 4095) (h_len : qs.length ≤ 252) :
    qs.sum < fheRs4096.t :=
  fold_sum_no_wrap qs 4095 252 _ h_each h_len (by decide)

/-- …and 253 is too many (`253·4095 ≥ t`): the u12 bound is tight too — every capacity pin in
this module is an equality-tight boundary, not a lazy under-claim. -/
theorem u12_capacity_tight : ¬ (253 * 4095 < fheRs4096.t) := by decide

/-- info: 'Minidregg.Theory.Bfv.fold_sum_no_wrap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_sum_no_wrap
/-- info: 'Minidregg.Theory.Bfv.fold_readout_faithful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_readout_faithful
/-- info: 'Minidregg.Theory.Bfv.wrap_misclears' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrap_misclears
/-- info: 'Minidregg.Theory.Bfv.u16_bucket_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms u16_bucket_capacity
/-- info: 'Minidregg.Theory.Bfv.sixteen_exceeds_t' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms sixteen_exceeds_t
/-- info: 'Minidregg.Theory.Bfv.sixteen_misclears' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms sixteen_misclears
/-- info: 'Minidregg.Theory.Bfv.u12_bucket_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms u12_bucket_capacity
/-- info: 'Minidregg.Theory.Bfv.u12_capacity_tight' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms u12_capacity_tight

end Minidregg.Theory.Bfv
