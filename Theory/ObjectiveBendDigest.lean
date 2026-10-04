/-
# Theory.ObjectiveBendDigest — Core4's `digest` primitive: what it computes and what it binds

`digest a b` (the Core4 primitive `Primitive.digest`, surface `digest(a, b)`) is the 32 output
bytes, read big-endian, of the kernel's cSHAKE256 (`Theory.Sp800185Cshake256Core`, the sponge
Pred's `hashEq` atom runs) under this primitive's own customization `DREGG.OBEND.DIGEST/v1`, over

    len(a):8 ‖ a ‖ b        (a, b as minimal big-endian bytes, `natBytesBE`; len big-endian)

It is total on every pair of naturals and always below `2^256` (`digest_lt`), so a digest is again
a first operand inside the binding domain and commitments nest: a sealed ballot is
`digest(digest(voter, vote), salt)`.

What is proved, and over which hash:

* `preimage_injective` — the encoding is injective whenever the first operand has fewer than `2^64`
  bytes (every `a < 2^256` does: `natBytesBE_length_le`).
* `binds_or_collides` — generic in the hash `H`: equal digests have equal operands, or `H` has a
  `Collision` (Theory.HashBytes, the carrier Pred's `hashEq` names). `sealed_binds_or_collides` is
  the nested ballot shape. Nothing about cSHAKE256 is assumed: the disjunct is where its collision
  resistance enters.
* `lengthHash_binding_fails` — the refutable pole: under a hash that reads only the input's length,
  any two second operands of one byte width have one digest. Binding is carried by the hash.
* `Hiding H Indistinguishable` — **ASSUMED, NOT PROVED** at `deployed`: no theorem here discharges
  it, and nothing displayed as "sealed" may claim more. Its poles at toy hashes: `constHash_hiding`
  (satisfied), `identity_not_hiding` (refuted), and `hiding_at_equality_is_a_collision` (at
  equality the assumption is itself a collision, so its meaning is only computational).

No proof here evaluates `deployed`: one Keccak-f[1600] permutation under kernel reduction is far
outside any proof budget. Closed instances at the deployed hash are in
`Theory.ObjectiveBendDigestChecks` (`native_decide`, pinned by `#assert_compiled`).

Relation to `Pred.hashEq`: deliberately a different function of the same sponge. `hashEq` binds a
cell, slot names and signed 32-byte words under `DREGG.PRED.HASHEQ/v2`; `digest` binds two
naturals under `DREGG.OBEND.DIGEST/v1`. The customization strings separate the two domains; no
theorem here relates their outputs, and a law that re-checks a program's commitment must call
`digest`, not `hashEq`.

Cost: one machine tick, as `multiply`; the sponge absorbs `1 + ⌈(|preimage| + 1) / 136⌉` blocks
(the framing block, then the padded input). The machine's tick does not price operand size for any
scalar primitive.

Init only (plus Theory.HashBytes and the cSHAKE256 leaf): the C transcription links this module's
compiled object and calls `minidregg_obend_digest`, so there is one implementation of the digest.
-/
import Theory.Sp800185Cshake256Core
import Theory.HashBytes

namespace Minidregg.Theory.ObjectiveBendDigest

open Minidregg.Theory.HashBytes
open Minidregg.Compiler.Sp800185Cshake256 (cshake256Bytes natBytesBE natBytesLE natBytesLEAux
  customizationPrefix padForRate absorbPadded squeeze32 rateBytes)

set_option autoImplicit false

/-! ## §1. Minimal big-endian bytes, read back -/

/-- Little-endian bytes read back as a natural (the C transcription's limb order). -/
def ofLE (bytes : List UInt8) : Nat := bytes.foldr (fun b acc => b.toNat + 256 * acc) 0

theorem ofLE_natBytesLEAux : ∀ (fuel n : Nat), n ≤ fuel → ofLE (natBytesLEAux fuel n) = n
  | 0, n, h => by
    have : n = 0 := by omega
    subst this; rfl
  | fuel + 1, n, h => by
    by_cases hn : n = 0
    · subst hn; simp [natBytesLEAux, ofLE]
    · have hq : n / 256 ≤ fuel := by omega
      have ih := ofLE_natBytesLEAux fuel (n / 256) hq
      simp only [natBytesLEAux, hn, if_false, ofLE, List.foldr_cons] at ih ⊢
      rw [ih, UInt8.toNat_ofNat']
      have h8 : (2 : Nat) ^ 8 = 256 := by decide
      rw [h8]
      omega

theorem ofBE_reverse : ∀ (bytes : List UInt8), ofBE bytes.reverse = ofLE bytes
  | [] => rfl
  | b :: rest => by
    rw [List.reverse_cons, ofBE_append_single, ofBE_reverse rest]
    simp only [ofLE, List.foldr_cons]
    omega

/-- `natBytesBE` is read back exactly: the encoding loses nothing. -/
theorem ofBE_natBytesBE (n : Nat) : ofBE (natBytesBE n) = n := by
  have hle := ofLE_natBytesLEAux n n (Nat.le_refl n)
  simp only [natBytesBE]
  split
  · next hnil =>
    have : n = 0 := by
      have h := hle; simp only [natBytesLE] at hnil; rw [hnil] at h; exact h.symm
    subst this; rfl
  · rw [ofBE_reverse]; exact hle

theorem natBytesBE_injective {n m : Nat} (h : natBytesBE n = natBytesBE m) : n = m := by
  rw [← ofBE_natBytesBE n, ← ofBE_natBytesBE m, h]

theorem natBytesLEAux_length_le : ∀ (fuel n k : Nat), n < 256 ^ k → (natBytesLEAux fuel n).length ≤ k
  | 0, _, _, _ => by simp [natBytesLEAux]
  | fuel + 1, n, k, h => by
    by_cases hn : n = 0
    · subst hn; simp [natBytesLEAux]
    · cases k with
      | zero => simp at h; omega
      | succ k =>
        have hpow : 256 ^ (k + 1) = 256 ^ k * 256 := Nat.pow_succ ..
        have hq : n / 256 < 256 ^ k := (Nat.div_lt_iff_lt_mul (by decide)).mpr (hpow ▸ h)
        have ih := natBytesLEAux_length_le fuel (n / 256) k hq
        simp only [natBytesLEAux, hn, if_false, List.length_cons]
        omega

/-- A natural below `256 ^ k` (`k ≥ 1`) takes at most `k` bytes. -/
theorem natBytesBE_length_le {n k : Nat} (hk : 0 < k) (h : n < 256 ^ k) :
    (natBytesBE n).length ≤ k := by
  have := natBytesLEAux_length_le n n k h
  simp only [natBytesBE]
  split <;> simp_all [natBytesLE] <;> omega

/-! ## §2. The preimage and its injectivity -/

/-- `len(a):8 ‖ a ‖ b`, both operands minimal big-endian. -/
def preimage (a b : Nat) : List UInt8 :=
  be 8 (natBytesBE a).length ++ natBytesBE a ++ natBytesBE b

/-- The binding domain: the first operand has fewer than `2^64` bytes. -/
def Admissible (a : Nat) : Prop := (natBytesBE a).length < 2 ^ 64

instance (a : Nat) : Decidable (Admissible a) := by unfold Admissible; infer_instance

/-- Every natural below `2^256` — every digest, every 32-byte salt — is admissible. -/
theorem admissible_of_lt {a : Nat} (h : a < 2 ^ 256) : Admissible a := by
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  have := natBytesBE_length_le (k := 32) (by decide) (h256 ▸ h)
  unfold Admissible
  omega

/-- **The encoding is injective on its domain.** Different operand pairs have different
preimages, so a digest equality between them is a collision of the hash. -/
theorem preimage_injective {a b a' b' : Nat} (ha : Admissible a) (ha' : Admissible a')
    (h : preimage a b = preimage a' b') : a = a' ∧ b = b' := by
  simp only [preimage, List.append_assoc] at h
  obtain ⟨hlen, h⟩ := List.append_inj h (by simp)
  have h64 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  have hl := be_injective (h64 ▸ ha) (h64 ▸ ha') hlen
  obtain ⟨hA, hB⟩ := List.append_inj h hl
  exact ⟨natBytesBE_injective hA, natBytesBE_injective hB⟩

/-! ## §3. The digest, generic in the hash, and its deployed instance -/

/-- The digest of `(a, b)` under the byte hash `H`, read big-endian. -/
def digestWith (H : Hash) (a b : Nat) : Nat := ofBE (H (preimage a b))

/-- This primitive's cSHAKE256 customization string. -/
def customization : List UInt8 := "DREGG.OBEND.DIGEST/v1".toUTF8.data.toList

/-- **The deployed hash**: the kernel's cSHAKE256 (empty function name, 256-bit output) under
`customization`. The compiled path is the word sponge of `Sp800185Cshake256Fast` (`@[csimp]`). -/
def deployed : Hash := cshake256Bytes customization

/-- **Core4's `digest`.** -/
def digest (a b : Nat) : Nat := digestWith deployed a b

/-- A digest is 32 bytes: always below `2^256`. -/
theorem digest_lt (a b : Nat) : digest a b < 2 ^ 256 := by
  have h := ofBE_lt (deployed (preimage a b))
  have hlen : (deployed (preimage a b)).length = 32 := by
    simp [deployed]
  rw [hlen] at h
  have h256 : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  simpa [digest, digestWith, h256] using h

/-- **Binds or collides.** Two operand pairs with one digest under `H` are the same pair, or `H`
has a collision. -/
theorem binds_or_collides (H : Hash) {a b a' b' : Nat} (ha : Admissible a) (ha' : Admissible a')
    (h : digestWith H a b = digestWith H a' b') : (a = a' ∧ b = b') ∨ Collision H := by
  by_cases hp : preimage a b = preimage a' b'
  · exact .inl (preimage_injective ha ha' hp)
  · exact .inr ⟨preimage a b, preimage a' b', hp, h⟩

/-- **The sealed-ballot shape.** `digest(digest(voter, vote), salt)` determines voter, vote and
salt, or cSHAKE256 (at this customization) has a collision. The inner digest is below `2^256`, so
the outer opening is always in the domain; the voter needs to be. -/
theorem sealed_binds_or_collides {v x s v' x' s' : Nat} (hv : v < 2 ^ 256) (hv' : v' < 2 ^ 256)
    (h : digest (digest v x) s = digest (digest v' x') s') :
    (v = v' ∧ x = x' ∧ s = s') ∨ Collision deployed := by
  rcases binds_or_collides deployed (admissible_of_lt (digest_lt v x))
      (admissible_of_lt (digest_lt v' x')) h with ⟨hin, hs⟩ | hcol
  · rcases binds_or_collides deployed (admissible_of_lt hv) (admissible_of_lt hv') hin with
      ⟨hvv, hxx⟩ | hcol
    · exact .inl ⟨hvv, hxx, hs⟩
    · exact .inr hcol
  · exact .inr hcol

/-! ## §4. The refutable pole: a length hash -/

/-- A hash that reads only the input's length. -/
def lengthHash : Hash := fun bytes => be 32 bytes.length

/-- **Under the length hash, binding fails**: every second operand of one byte width gives one
digest. So `binds_or_collides` is carried by the hash, not by the encoding. -/
theorem lengthHash_binding_fails (a b b' : Nat)
    (hw : (natBytesBE b).length = (natBytesBE b').length) :
    digestWith lengthHash a b = digestWith lengthHash a b' := by
  simp only [digestWith, lengthHash, preimage, List.length_append, hw]

/-- The collision disjunct is reachable: the length hash has one (operands `(0, 1)`, `(0, 2)`). -/
theorem lengthHash_collides : Collision lengthHash :=
  ⟨preimage 0 1, preimage 0 2, by decide,
    lengthHash_binding_fails 0 1 2 (by decide)⟩

/-! ## §5. Hiding — ASSUMED, not proved

A commitment `digestWith H x salt` hides `x` when, for a uniform 32-byte `salt`, the commitments to
any two `x` are indistinguishable. That is a computational property of cSHAKE256 (in the random-
oracle model a `q`-query distinguisher's advantage is about `q / 2^256`), and this tree has no model
in which to state "feasible". It is named here as an assumption over a hash and a supplied
relation; the deployed reading is `Hiding deployed`, discharged nowhere. -/

/-- **ASSUMED, NOT PROVED (at `deployed`).** For every two committed values, the commitment as a
function of the salt is `Indistinguishable`. Meaningful only at a computational relation over
uniform 32-byte salts; this tree supplies none. -/
def Hiding (H : Hash) (Indistinguishable : (Nat → Nat) → (Nat → Nat) → Prop) : Prop :=
  ∀ x x' : Nat, Indistinguishable (fun salt => digestWith H x salt) (fun salt => digestWith H x' salt)

/-- A hash that ignores its input. -/
def constHash : Hash := fun _ => be 32 0

/-- **Satisfiable** (toy hash): a constant hash hides at the strongest relation, equality. -/
theorem constHash_hiding : Hiding constHash (· = ·) := fun _ _ => rfl

/-- **Refutable** (toy hash): the identity "hash" puts the committed value in the commitment. -/
theorem identity_not_hiding : ¬ Hiding id (· = ·) := by
  intro h
  have e := congrFun (h 0 1) 0
  revert e
  decide

/-- The assumption cannot be read as equality: hiding at `=` makes `0` and `1` commit identically,
which is a collision of the same hash. -/
theorem hiding_at_equality_is_a_collision (H : Hash) (h : Hiding H (· = ·)) : Collision H := by
  have a0 : Admissible 0 := admissible_of_lt (by decide)
  have a1 : Admissible 1 := admissible_of_lt (by decide)
  rcases binds_or_collides H a0 a1 (congrFun (h 0 1) 0) with ⟨h01, -⟩ | hcol
  · exact absurd h01 (by decide)
  · exact hcol

/-! ## §6. Cost: Keccak-f[1600] permutations per digest

A digest step is one machine tick (as every primitive), but the work behind it is
`permutations a b` Keccak-f[1600] permutations of 24 rounds: the framing block, then the padded
preimage. Under a scalar capacity of `8 k` bits (both operands below `256 ^ k`) that is at most
`(8 + 2 k) / 136 + 2`: **≤ 2 at 256-bit operands, ≤ 3 at 512-bit operands** (the native acceptance
capacity, `scalarBits = 512`). The tick does not weigh it; a size-aware meter is a separate row. -/

/-- `deployed` spelled out: frame, absorb the padded input, squeeze 32 bytes. -/
theorem deployed_eq (input : List UInt8) :
    deployed input = squeeze32 (absorbPadded (padForRate (customizationPrefix customization ++ input) 0x04)) := by
  have hne : (customization = []) = False := by
    apply propext; constructor
    · intro h; have := congrArg List.length h; revert this; decide
    · intro h; cases h
  simp only [deployed, cshake256Bytes, hne, if_false]

/-- The permutations `deployed` runs on `preimage a b`: `absorbPadded` runs Keccak-f[1600] once per
`rateBytes` block of the padded input (its definition); squeezing 32 bytes runs none. -/
def permutations (a b : Nat) : Nat :=
  (padForRate (customizationPrefix customization ++ preimage a b) 0x04).length / rateBytes

theorem customizationPrefix_length : (customizationPrefix customization).length = 136 := by
  decide +kernel

theorem padForRate_length (bytes : List UInt8) (suffix : UInt8) :
    (padForRate bytes suffix).length = (bytes.length / 136 + 1) * 136 := by
  unfold padForRate rateBytes
  dsimp only
  split <;> simp <;> omega

theorem permutations_eq (a b : Nat) : permutations a b = (preimage a b).length / 136 + 2 := by
  simp only [permutations, padForRate_length, List.length_append, customizationPrefix_length,
    rateBytes]
  omega

theorem preimage_length (a b : Nat) :
    (preimage a b).length = 8 + (natBytesBE a).length + (natBytesBE b).length := by
  simp [preimage]
  omega

/-- **The per-step bound.** Operands below `256 ^ k` cost at most `(8 + 2 k) / 136 + 2`
permutations. -/
theorem permutations_le {a b k : Nat} (hk : 0 < k) (ha : a < 256 ^ k) (hb : b < 256 ^ k) :
    permutations a b ≤ (8 + 2 * k) / 136 + 2 := by
  have la := natBytesBE_length_le hk ha
  have lb := natBytesBE_length_le hk hb
  rw [permutations_eq, preimage_length]
  have := Nat.div_le_div_right (c := 136)
    (show 8 + (natBytesBE a).length + (natBytesBE b).length ≤ 8 + 2 * k by omega)
  omega

set_option exponentiation.threshold 512 in
/-- At the native acceptance capacity (`scalarBits = 512`): at most three permutations. -/
theorem permutations_le_three {a b : Nat} (ha : a < 2 ^ 512) (hb : b < 2 ^ 512) :
    permutations a b ≤ 3 := by
  have h : (2 : Nat) ^ 512 = 256 ^ 64 := by
    rw [show (512 : Nat) = 8 * 64 by rfl, Nat.pow_mul]
  have := permutations_le (k := 64) (by decide) (Nat.lt_of_lt_of_eq ha h) (Nat.lt_of_lt_of_eq hb h)
  omega

/-- At 256-bit operands (a digest and a 32-byte salt, the sealed ballot's outer step): two. -/
theorem permutations_le_two {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    permutations a b ≤ 2 := by
  have h : (2 : Nat) ^ 256 = 256 ^ 32 := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
  have := permutations_le (k := 32) (by decide) (h ▸ ha) (h ▸ hb)
  omega

/-! ## §7. The C entry

The C transcription (`native/objective-emit/runtime.c`) links this module's compiled object and
calls this export for `P_DIGEST`: it passes each operand's limbs as little-endian bytes and reads the
32 big-endian digest bytes back. It computes no part of the digest itself. -/

/-- The digest of two little-endian operands, as 32 big-endian bytes. -/
@[export minidregg_obend_digest]
def digestExport (a b : ByteArray) : ByteArray :=
  ⟨(be 32 (digest (ofLE a.data.toList) (ofLE b.data.toList))).toArray⟩

/-- The export returns exactly `digest` of the operands it was handed, in 32 bytes. -/
theorem digestExport_reads (a b : ByteArray) :
    ofBE (digestExport a b).data.toList = digest (ofLE a.data.toList) (ofLE b.data.toList) ∧
      (digestExport a b).data.toList.length = 32 := by
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  refine ⟨?_, by simp [digestExport]⟩
  simp only [digestExport]
  exact ofBE_be (h256 ▸ digest_lt _ _)

end Minidregg.Theory.ObjectiveBendDigest
