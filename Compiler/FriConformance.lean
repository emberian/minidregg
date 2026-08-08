/-
# `Compiler/FriConformance.lean` — `[PROVER-fri-fold]`'s conformance vector

**Substrate, said out loud: this file is a verified-side reference computation for the
seam.** The UNVERIFIED Rust prover (`prover/src/fri.rs` + `prover/src/field4.rs`) adopts
breadstuffs' FRI fold kernel (the MATH of `hidingfri_fold_ext4.wgsl`, never its Plonky3
harness); Rust has no formal semantics, so the seam is a CONFORMANCE VECTOR: this file
instantiates the REAL `Loom/Proximity.lean` `fold` — the object `fold_preserves_code` /
`proximity_sound` are about — on a concrete 16-point two-adic BabyBear domain, pins the
folded words IN THE KERNEL, and writes `prover/testdata/fri_conformance.json`; the Rust
test reproduces them with its own twiddle-form fold. Agreement on the vector is the
whole claim — never refinement.

## The vector's teeth

* **The twiddle convention is pinned.** Loom's fold divides — `(f(x)+f(−x))/2 +
  β·(f(x)−f(−x))/(2x)` — while the deployed kernel multiplies by precomputed `½·g⁻ʲ`
  twiddles. The literals below were computed twiddle-style and are proved equal to
  Loom's `fold` via `fold_eq_of_mul_eq` (a division-free characterization; its numeric
  leaf is kernel-decided), so the JSON values ARE the verified fold's outputs as a
  THEOREM, and a twiddle-indexing or halving drift in Rust fails the vector. All 16
  codeword values are distinct, so pairing/indexing flips fail too.
* **The arity schedule is pinned.** `friFolded2 = Loom.fold (fold f β) β²` — the arity-4
  fold's β-squaring chain, cross-checked by the Rust `log_arity = 2` path.
* **The domain is the canonical one.** `friGen16` has exact order 16 (`g⁸ = −1`,
  kernel-decided) and the embedding IS its power sequence (decided); the Rust side
  checks the serialized generator equals ITS `two_adic_generator(4)` descended from
  `31¹⁵ mod p` — tying the Lean domain to the deployed twiddle generation.
* **The extension multiplication is a THEOREM, then a vector.** `ext4Mul` — the
  deployed kernel's BabyBear⁴ formula (X⁴ = 11) — is proved to BE multiplication in
  the quotient ring `BabyBear[X]/(X⁴ − 11)` (`ext4Mul_correct`, via `AdjoinRoot`; no
  irreducibility needed for multiplication), and two kernel-decided known-answer
  products (one with all lanes at the modulus edge) ride the JSON for the Rust
  `Ext4::mul` to reproduce.

## Honest scope limits

* Loom's `fold` is instantiated at the BASE field: Loom holds the degree-4 extension
  abstractly (`Loom/SmallField.lean`'s `Algebra Fq K`, the `GaloisField` keystone) —
  there is NO computable BabyBear⁴ field instance to `#eval` through `fold`. So the
  fold vector exercises the Rust fold's full code path on base-embedded lanes, and the
  cross-lane multiplication is pinned separately by `ext4Mul_correct` + the product
  vectors. Ext-valued fold conformance needs a computable verified BabyBear⁴ —
  flagged, not hidden.
* NOT claimed: irreducibility of `X⁴ − 11` over BabyBear (that the quotient is a
  FIELD, so `Loom/SmallField`'s `|F| = p⁴` pricing applies to THIS concrete quotient)
  — named residual `[PROVER-field-ext4-irred]`.

The Lean side is the only author of `prover/testdata/fri_conformance.json`; Rust only
reads. `Loom/` cannot host this file — the import boundary rightly keeps
`Lean.Data.Json` out of the proof layer — so it lives here beside the other
conformance vectors.
-/
import Mathlib.RingTheory.AdjoinRoot
import Compiler.EmitSerialize
import Loom.Proximity

namespace Minidregg.Compiler

open Minidregg.Loom
open Polynomial
open Lean (Json ToJson toJson)

/-! ## §1. The division-free characterization of the verified fold

Loom's `fold` divides; the kernel cannot decide division (`ZMod.inv` is
well-founded recursion). The bridge: `Fold(f,α)(k)` is the UNIQUE `y` with
`2x·y = x·(f(x)+f(−x)) + α·(f(x)−f(−x))` (where `x = dom (sec k) ≠ 0`), and THAT
equation is division-free, hence kernel-decidable on literals. -/

/-- The verified fold, characterized without division: if `g` satisfies the
cleared-denominator identity at every folded point, it IS `Loom.fold D f α`. -/
theorem fold_eq_of_mul_eq {F : Type*} [Field F] {ι κ : Type*}
    {dom : ι ↪ F} {domSq : κ ↪ F} (D : FoldingData F dom domSq)
    (f : ι → F) (α : F) (g : κ → F)
    (h : ∀ k, (2 * dom (D.sec k)) * g k
        = dom (D.sec k) * (f (D.sec k) + f (D.neg (D.sec k)))
          + α * (f (D.sec k) - f (D.neg (D.sec k)))) :
    Loom.fold D f α = g := by
  funext k
  have hx : dom (D.sec k) ≠ 0 := D.dom_ne_zero (D.sec k)
  have h2 : (2 : F) ≠ 0 := D.two_ne
  have h2x : (2 : F) * dom (D.sec k) ≠ 0 := mul_ne_zero h2 hx
  have hg : g k = (dom (D.sec k) * (f (D.sec k) + f (D.neg (D.sec k)))
      + α * (f (D.sec k) - f (D.neg (D.sec k)))) / (2 * dom (D.sec k)) := by
    rw [← h k, mul_div_cancel_left₀ _ h2x]
  show Loom.foldEven D f k + α * Loom.foldOdd D f k = g k
  rw [Loom.foldEven, Loom.foldOdd, hg]
  field_simp

/-! ## §2. The 16-point two-adic domain and its folding tower

`friGen16 = 31^(15·2^23) mod p` — the canonical order-16 element of BabyBear's
2-adic subgroup (the Rust side re-derives it from `31^15` and checks the JSON).
Levels: 16 → 8 → 4 points, embeddings listed as literals (decided to be the
power sequences), negation `j ↦ j + n/2` (`g^(n/2) = −1`), squaring `j ↦ j mod
n/2`, section = the first-half root. -/

/-- The canonical order-16 generator of BabyBear's 2-adic subgroup. -/
def friGen16 : BabyBear := 196396260

example : friGen16 ^ 8 = -1 := by decide
example : friGen16 ^ 16 = 1 := by decide

/-- Level 0: the order-16 subgroup, `j ↦ g^j`. -/
def friDom16 : Fin 16 ↪ BabyBear :=
  ⟨![1, 196396260, 1592366214, 78945800, 1728404513, 1400279418, 211723194,
     1446056615, 2013265920, 1816869661, 420899707, 1934320121, 284861408,
     612986503, 1801542727, 567209306], by decide⟩

/-- Level 1: the order-8 subgroup of squares, `k ↦ (g²)^k`. -/
def friDom8 : Fin 8 ↪ BabyBear :=
  ⟨![1, 1592366214, 1728404513, 211723194, 2013265920, 420899707, 284861408,
     1801542727], by decide⟩

/-- Level 2: the order-4 subgroup, `k ↦ (g⁴)^k`. -/
def friDom4 : Fin 4 ↪ BabyBear :=
  ⟨![1, 1728404513, 2013265920, 284861408], by decide⟩

/-- The level-0 embedding IS the generator's power sequence (pinned). -/
example : ∀ j : Fin 16, friDom16 j = friGen16 ^ (j : ℕ) := by decide

/-- Folding structure 16 → 8: negation `j ↦ j+8`, squaring `j ↦ j mod 8`,
section = first-half root. Every law kernel-decided. -/
def friData16 : FoldingData BabyBear friDom16 friDom8 where
  neg := ![8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]
  dom_neg := by decide
  sq := ![0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7]
  domSq_sq := by decide
  sec := ![0, 1, 2, 3, 4, 5, 6, 7]
  sq_sec := by decide
  dom_ne_zero := by decide
  two_ne := by decide

/-- Folding structure 8 → 4, same shape. -/
def friData8 : FoldingData BabyBear friDom8 friDom4 where
  neg := ![4, 5, 6, 7, 0, 1, 2, 3]
  dom_neg := by decide
  sq := ![0, 1, 2, 3, 0, 1, 2, 3]
  domSq_sq := by decide
  sec := ![0, 1, 2, 3]
  sq_sec := by decide
  dom_ne_zero := by decide
  two_ne := by decide

/-! ## §3. The fold vector: word, challenges, folded words — kernel-pinned -/

/-- The conformance codeword: 16 distinct BabyBear values (one at `p − 1` to
exercise the modulus), asymmetric so index flips fail. NOT a codeword of low
degree — the fold vector pins arithmetic, not completeness (that is Loom's
`fold_preserves_code`, a theorem). -/
def friWord : Fin 16 → BabyBear :=
  ![123456789, 987654321, 555555555, 2013265920, 42, 777000777, 31415926,
    271828182, 1414213562, 1732050807, 1010101010, 909090909, 606060606,
    1234567891, 1999999999, 7]

/-- The fixed fold challenge (Fiat-Shamir drawing is `[PROVER-fs]`, not this
rung). Base-field valued: see the honest scope limits in the header. -/
def friBeta : BabyBear := 1122334455

/-- Round 1's folded word, `Loom.fold friData16 friWord friBeta` (proved below). -/
def friFolded1 : Fin 8 → BabyBear :=
  ![239119039, 660932314, 1863219774, 1822133813, 1708817283, 508441011,
    414370117, 192632238]

/-- `β²` — the second-round challenge of the arity-4 fold. -/
def friBetaSq : BabyBear := 65254777

theorem friBetaSq_eq : friBeta * friBeta = friBetaSq := by decide

/-- Round 2's folded word, `Loom.fold friData8 friFolded1 friBetaSq` (proved below). -/
def friFolded2 : Fin 4 → BabyBear :=
  ![40624829, 1598776887, 449075122, 1359015159]

/-- **The serialized literals ARE Loom's verified fold** (round 1): theorem, with
the numeric leaf kernel-decided through the division-free characterization. -/
theorem friFolded1_eq : Loom.fold friData16 friWord friBeta = friFolded1 :=
  fold_eq_of_mul_eq friData16 friWord friBeta friFolded1 (by decide)

/-- Round 2, at challenge `β²`: the arity-4 chain `Loom.fold (fold f β) β²`. -/
theorem friFolded2_eq : Loom.fold friData8 friFolded1 friBetaSq = friFolded2 :=
  fold_eq_of_mul_eq friData8 friFolded1 friBetaSq friFolded2 (by decide)

/-- The two rounds compose: `friFolded2` is the arity-4 fold of the original
word under the β-squaring schedule — the exact chain the Rust `log_arity = 2`
path computes. -/
theorem friFolded2_is_arity4 :
    Loom.fold friData8 (Loom.fold friData16 friWord friBeta) friBetaSq = friFolded2 := by
  rw [friFolded1_eq, friFolded2_eq]

/-! ## §4. BabyBear⁴: the deployed extension-multiplication formula, proved

The kernel's `ext_mul` (X⁴ = 11) as a Lean function, proved to be multiplication
in the quotient ring `BabyBear[X]/(X⁴ − 11)` — well-defined for ANY monic
modulus, no irreducibility needed (inverses, which would need it, are nowhere in
the fold). -/

/-- The deployed BabyBear⁴ multiplication formula (X⁴ = 11), lane form. -/
def ext4Mul (a b : Fin 4 → BabyBear) : Fin 4 → BabyBear
  | 0 => a 0 * b 0 + 11 * (a 1 * b 3 + a 2 * b 2 + a 3 * b 1)
  | 1 => a 0 * b 1 + a 1 * b 0 + 11 * (a 2 * b 3 + a 3 * b 2)
  | 2 => a 0 * b 2 + a 1 * b 1 + a 2 * b 0 + 11 * (a 3 * b 3)
  | 3 => a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0

/-- The quotient ring `BabyBear[X]/(X⁴ − 11)` — BabyBear⁴ as a ring (field-ness
is `[PROVER-field-ext4-irred]`, not claimed). -/
noncomputable abbrev Ext4Q : Type := AdjoinRoot ((X : Polynomial BabyBear) ^ 4 - C 11)

/-- The image of `X` in the quotient. -/
noncomputable def ext4Root : Ext4Q := AdjoinRoot.root _

/-- A lane vector as a quotient-ring element: `v₀ + v₁X + v₂X² + v₃X³`. -/
noncomputable def toExt4 (v : Fin 4 → BabyBear) : Ext4Q :=
  AdjoinRoot.of _ (v 0) + AdjoinRoot.of _ (v 1) * ext4Root
    + AdjoinRoot.of _ (v 2) * ext4Root ^ 2 + AdjoinRoot.of _ (v 3) * ext4Root ^ 3

/-- The defining relation: `X⁴ = 11` in the quotient. -/
theorem ext4Root_pow_four : ext4Root ^ 4 = AdjoinRoot.of _ (11 : BabyBear) := by
  have h := AdjoinRoot.mk_self (f := (X : Polynomial BabyBear) ^ 4 - C 11)
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
  exact h

/-- The lane formula against the ring, as pure algebra: reducing `r⁴ ↦ w` in the
convolution product. -/
private theorem ext4_mul_ring {R : Type*} [CommRing R]
    (a0 a1 a2 a3 b0 b1 b2 b3 r w : R) (h : r ^ 4 = w) :
    a0 * b0 + w * (a1 * b3 + a2 * b2 + a3 * b1)
      + (a0 * b1 + a1 * b0 + w * (a2 * b3 + a3 * b2)) * r
      + (a0 * b2 + a1 * b1 + a2 * b0 + w * (a3 * b3)) * r ^ 2
      + (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) * r ^ 3
    = (a0 + a1 * r + a2 * r ^ 2 + a3 * r ^ 3)
        * (b0 + b1 * r + b2 * r ^ 2 + b3 * r ^ 3) := by
  linear_combination
    (-(a1 * b3 + a2 * b2 + a3 * b1) - (a2 * b3 + a3 * b2) * r - a3 * b3 * r ^ 2) * h

/-- **The deployed `ext_mul` formula IS multiplication in `BabyBear[X]/(X⁴−11)`.**
The Rust `Ext4::mul` mirrors this formula; the known-answer vectors below carry
it across the seam. -/
theorem ext4Mul_correct (a b : Fin 4 → BabyBear) :
    toExt4 (ext4Mul a b) = toExt4 a * toExt4 b := by
  simp only [toExt4, ext4Mul, map_add, map_mul]
  linear_combination
    ext4_mul_ring (AdjoinRoot.of _ (a 0)) (AdjoinRoot.of _ (a 1))
      (AdjoinRoot.of _ (a 2)) (AdjoinRoot.of _ (a 3))
      (AdjoinRoot.of _ (b 0)) (AdjoinRoot.of _ (b 1))
      (AdjoinRoot.of _ (b 2)) (AdjoinRoot.of _ (b 3))
      ext4Root (AdjoinRoot.of _ (11 : BabyBear)) ext4Root_pow_four

/-- The defining relation, computed through the formula: `x⁴ = 11`. -/
example :
    ext4Mul ![0, 1, 0, 0] (ext4Mul ![0, 1, 0, 0] (ext4Mul ![0, 1, 0, 0] ![0, 1, 0, 0]))
      = ![11, 0, 0, 0] := by decide

/-- Known-answer product 1: generic lanes (one at `p − 1`). -/
def extA : Fin 4 → BabyBear := ![123456789, 987654321, 555555555, 2013265920]
def extB : Fin 4 → BabyBear := ![1999999999, 42, 1414213562, 777000777]
def extProd : Fin 4 → BabyBear := ![1366462123, 4184375, 1911137655, 456494622]

example : ext4Mul extA extB = extProd := by decide

/-- Known-answer product 2: all lanes at the modulus edge (wraparound teeth). -/
def extA2 : Fin 4 → BabyBear := ![2013265920, 2013265919, 2013265918, 2013265917]
def extB2 : Fin 4 → BabyBear := ![1, 2, 3, 2013265920]
def extProd2 : Fin 4 → BabyBear := ![2013265755, 2013265818, 34, 2013265906]

example : ext4Mul extA2 extB2 = extProd2 := by decide

/-! ## §5. The writer — same discipline as the other conformance vectors -/

/-- The whole conformance file: field, domain generator, codeword, the two
challenges, both Loom-computed folded words (theorem-pinned above), and the
extension-multiplication known-answer vectors. -/
def friConformanceJson : Json :=
  Json.mkObj
    [ ("p", toJson babyBearP),
      ("logN", toJson (4 : ℕ)),
      ("gen", toJson friGen16.val),
      ("codeword", finVecToJson friWord),
      ("beta", toJson friBeta.val),
      ("folded1", finVecToJson friFolded1),
      ("betaSq", toJson friBetaSq.val),
      ("folded2", finVecToJson friFolded2),
      ("extW", toJson (11 : ℕ)),
      ("extA", finVecToJson extA),
      ("extB", finVecToJson extB),
      ("extProd", finVecToJson extProd),
      ("extA2", finVecToJson extA2),
      ("extB2", finVecToJson extB2),
      ("extProd2", finVecToJson extProd2) ]

/-- Write the conformance file (creating the parent directory; repo-root-relative). -/
def writeFriConformance (path : System.FilePath) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path (friConformanceJson.pretty ++ "\n")

#eval writeFriConformance "prover/testdata/fri_conformance.json"

end Minidregg.Compiler
