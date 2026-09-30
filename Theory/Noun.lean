/-
# Theory.Noun — Nock nouns, axis/edit, and Hoon's `jam`/`cue`

A noun is an atom (a natural number) or a cell (an ordered pair of nouns).
`jam`/`cue` are Hoon's self-delimiting bit codec with back-references
(`hoon-138.hoon:1939-2005` at nockchain `cbd9298f`; Rust
`crates/nockvm/rust/nockvm/src/serialization.rs:125,458`), built here as the
same algorithm: a noun seen before is emitted as a back-reference to the bit
position of its first emission, except an atom whose own bit length does not
exceed the reference's, which is emitted inline again.

Byte order: the jam is an atom; its bytes are that atom's little-endian bytes
(bit `i` of the stream is bit `i mod 8` of byte `i / 8`). The last emitted bit
of every jam is `1`, so the byte list has no trailing zero byte.

`cue_jam` is the round trip; `jam_injective` its corollary. `cue` is not the
inverse of `jam` on all inputs: an atom may be emitted with a non-minimal
length prefix, a back-reference may be spelled inline, and trailing bits are
ignored, so several byte strings cue to one noun. `canonical` names the one
`jam` produces and `canonical_unique` says it is unique per noun.

Every function here is structurally recursive, so small instances evaluate by
`decide` in the kernel; nothing hashes.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

namespace Minidregg.Theory

/-- A Nock noun: an atom (any natural) or a cell. -/
inductive Noun where
  | atom (n : Nat)
  | cell (h t : Noun)
  deriving DecidableEq, Repr, Inhabited

namespace Noun

/-- Number of constructors (the unshared tree size). -/
def size : Noun → Nat
  | atom _ => 1
  | cell h t => h.size + t.size + 1

/-- Depth of the tree; an atom has depth 0. -/
def depth : Noun → Nat
  | atom _ => 0
  | cell h t => max h.depth t.depth + 1

theorem size_pos (n : Noun) : 0 < n.size := by cases n <;> simp [size]

/-- Nock's loobean: `0` is yes, `1` is no. -/
def loob (b : Bool) : Noun := atom (if b then 0 else 1)

def isCell : Noun → Bool
  | atom _ => false
  | cell _ _ => true

/-! ## Axis (`/`) and edit (`#`) -/

/-- Fuel-bounded axis walk; `axis a` uses fuel `a`, which is always enough
since the recursion halves the axis. -/
def axisAux : Nat → Nat → Noun → Option Noun
  | 0, _, _ => none
  | k + 1, a, n =>
    if a = 0 then none
    else if a = 1 then some n
    else
      match axisAux k (a / 2) n with
      | some (cell h t) => some (if a % 2 = 0 then h else t)
      | _ => none

/-- `/[a n]`: `1` is the noun, `2`/`3` head/tail, `2a`/`2a+1` head/tail of
`/[a n]`; axis `0` and any walk into an atom have no value. -/
def axis (a : Nat) (n : Noun) : Option Noun := axisAux a a n

/-- Fuel-bounded edit: `#[1 v t] = v`, `#[2a v t] = #[a [v /[2a+1 t]] t]`,
`#[2a+1 v t] = #[a [/[2a t] v] t]`. -/
def editAux : Nat → Nat → Noun → Noun → Option Noun
  | 0, _, _, _ => none
  | k + 1, a, v, t =>
    if a = 0 then none
    else if a = 1 then some v
    else
      match axis (a / 2) t with
      | some (cell h tl) => editAux k (a / 2) (if a % 2 = 0 then cell v tl else cell h v) t
      | _ => none

/-- `#[a v t]`: replace the subtree of `t` at axis `a` by `v`. -/
def edit (a : Nat) (v t : Noun) : Option Noun := editAux a a v t

/-! ## Bits -/

/-- The low `k` bits of `n`, least significant first. -/
def natBits : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, n => (n % 2 == 1) :: natBits k (n / 2)

/-- Little-endian bit list to its value. -/
def ofBits : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * ofBits bs

def bitLenAux : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => if n = 0 then 0 else bitLenAux k (n / 2) + 1

/-- Hoon's `(met 0 n)`: the number of significant bits (`0` for `0`). -/
def bitLen (n : Nat) : Nat := bitLenAux n n

/-- Hoon's `++mat`: `c` zeros, a one, the low `c-1` bits of `b = met 0 n`,
then the `b` bits of `n`, where `c = met 0 b`; `0` is the single bit `1`. -/
def mat (n : Nat) : List Bool :=
  if n = 0 then [true]
  else
    List.replicate (bitLen (bitLen n)) false ++
      true :: (natBits (bitLen (bitLen n) - 1) (bitLen n) ++ natBits (bitLen n) n)

/-! ## jam -/

/-- The back-reference table: noun ↦ bit position of its first emission. -/
abbrev JamTable := List (Noun × Nat)

def lookupPos (a : Noun) : JamTable → Option Nat
  | [] => none
  | (k, v) :: r => if a = k then some v else lookupPos a r

/-- Emit `n` starting at bit position `pos` with table `m`; returns the bits
emitted and the new table (Hoon `++jam`'s inner gate). -/
def jamAux : Noun → JamTable → Nat → List Bool × JamTable
  | atom a, m, pos =>
    match lookupPos (atom a) m with
    | some p =>
      if bitLen a ≤ bitLen p then (false :: mat a, m)
      else (true :: true :: mat p, m)
    | none => (false :: mat a, (atom a, pos) :: m)
  | cell h t, m, pos =>
    match lookupPos (cell h t) m with
    | some p => (true :: true :: mat p, m)
    | none =>
      let m1 := (cell h t, pos) :: m
      let rh := jamAux h m1 (pos + 2)
      let rt := jamAux t rh.2 (pos + 2 + rh.1.length)
      (true :: false :: (rh.1 ++ rt.1), rt.2)

/-- The jam bit stream of a noun. -/
def jamBits (n : Noun) : List Bool := (jamAux n [] 0).1

/-- Pack a little-endian bit stream into bytes (last byte zero-padded). -/
def toBytesAux : Nat → List Bool → List UInt8
  | 0, _ => []
  | k + 1, bs => if bs = [] then [] else (ofBits (bs.take 8)).toUInt8 :: toBytesAux k (bs.drop 8)

def toBytes (bs : List Bool) : List UInt8 := toBytesAux bs.length bs

/-- The bits of a byte list, byte 0 bit 0 first. -/
def fromBytes : List UInt8 → List Bool
  | [] => []
  | b :: r => natBits 8 b.toNat ++ fromBytes r

/-- Hoon's `++jam`, as the atom's little-endian bytes. -/
def jam (n : Noun) : List UInt8 := toBytes (jamBits n)

/-! ## cue -/

/-- Count zeros from bit `i` up to the first one (tail-recursive). -/
def countZeros (B : Array Bool) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | k + 1, i, c =>
    match B[i]? with
    | none => none
    | some true => some c
    | some false => countZeros B k (i + 1) (c + 1)

/-- Read `l` bits from position `i` as a little-endian number (tail-recursive):
`acc + pw * value`. -/
def readBits (B : Array Bool) : Nat → Nat → Nat → Nat → Option Nat
  | 0, _, acc, _ => some acc
  | l + 1, i, acc, pw =>
    match B[i]? with
    | none => none
    | some b => readBits B l (i + 1) (if b then acc + pw else acc) (2 * pw)

/-- Hoon's `++rub` at bit `i`: the value and the next cursor. -/
def rub (B : Array Bool) (i : Nat) : Option (Nat × Nat) :=
  match countZeros B B.size i 0 with
  | none => none
  | some c =>
    if c = 0 then some (0, i + 1)
    else
      match readBits B (c - 1) (i + c + 1) 0 1 with
      | none => none
      | some x =>
        let b := 2 ^ (c - 1) + x
        match readBits B b (i + c + c) 0 1 with
        | none => none
        | some v => some (v, i + c + c + b)

/-- The decode table: bit position ↦ the noun that started there (a cell's
entry is written only after both children decode, as in Hoon's `++cue`). -/
abbrev CueTable := Array (Option Noun)

/-- Decode one noun at bit `i` (fuel bounds recursion depth). -/
def decode (B : Array Bool) : Nat → Nat → CueTable → Option (Noun × Nat × CueTable)
  | 0, _, _ => none
  | k + 1, i, t =>
    match B[i]? with
    | none => none
    | some false =>
      match rub B (i + 1) with
      | none => none
      | some (v, j) => some (atom v, j, t.setIfInBounds i (some (atom v)))
    | some true =>
      match B[i + 1]? with
      | none => none
      | some false =>
        match decode B k (i + 2) t with
        | none => none
        | some (h, j, t1) =>
          match decode B k j t1 with
          | none => none
          | some (tl, j2, t2) => some (cell h tl, j2, t2.setIfInBounds i (some (cell h tl)))
      | some true =>
        match rub B (i + 2) with
        | none => none
        | some (p, j) =>
          match t[p]? with
          | some (some n) => some (n, j, t)
          | _ => none

/-- Hoon's `++cue` over the little-endian bytes of the jam atom; `none` on any
malformed prefix (a read past the end, a back-reference to a position where no
completed noun started). Bits after the decoded noun are ignored. -/
def cue (bs : List UInt8) : Option Noun :=
  let B := (fromBytes bs).toArray
  match decode B B.size 0 (Array.replicate B.size none) with
  | none => none
  | some (n, _, _) => some n

/-- The byte string `jam` produces for the noun it cues to. -/
def canonical (bs : List UInt8) : Bool := (cue bs).map jam == some bs

/-! ## Integers -/

/-- Zigzag: `0,-1,1,-2,2,… ↦ 0,1,2,3,4,…`. -/
def _root_.Int.toNoun (z : Int) : Noun :=
  match z with
  | .ofNat n => atom (2 * n)
  | .negSucc n => atom (2 * n + 1)

def toInt? : Noun → Option Int
  | atom n => some (if n % 2 = 0 then .ofNat (n / 2) else .negSucc (n / 2))
  | cell _ _ => none


/-! ## Bit lemmas -/

theorem natBits_length : ∀ k n, (natBits k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [natBits, natBits_length k]

theorem mod_two_mul (n M : Nat) (hM : 0 < M) :
    n % (2 * M) = n % 2 + 2 * (n / 2 % M) := by
  have hn := (Nat.div_add_mod n 2).symm
  have h1 := Nat.div_add_mod (n / 2) M
  have h2 := Nat.mod_lt (n / 2) hM
  have h3 := Nat.mod_lt n (show 0 < 2 by omega)
  have e : n = (n % 2 + 2 * (n / 2 % M)) + 2 * M * (n / 2 / M) := by
    rw [Nat.mul_assoc]; generalize M * (n / 2 / M) = X at *; omega
  conv_lhs => rw [e]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem ofBits_natBits : ∀ k n, ofBits (natBits k n) = n % 2 ^ k
  | 0, n => by simp [natBits, ofBits, Nat.mod_one]
  | k + 1, n => by
    simp only [natBits, ofBits, ofBits_natBits k]
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, mod_two_mul n _ (Nat.two_pow_pos k)]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem ofBits_append (l₁ l₂ : List Bool) :
    ofBits (l₁ ++ l₂) = ofBits l₁ + 2 ^ l₁.length * ofBits l₂ := by
  induction l₁ with
  | nil => simp [ofBits]
  | cons b r ih => simp only [List.cons_append, ofBits, ih, List.length_cons, Nat.pow_succ]; ring_nf

theorem ofBits_lt : ∀ l : List Bool, ofBits l < 2 ^ l.length
  | [] => by simp [ofBits]
  | b :: r => by
    have := ofBits_lt r
    simp only [ofBits, List.length_cons, Nat.pow_succ]
    split <;> omega

theorem natBits_zero : ∀ k, natBits k 0 = List.replicate k false
  | 0 => rfl
  | k + 1 => by simp [natBits, natBits_zero k, List.replicate_succ]

theorem natBits_ofBits : ∀ (l : List Bool) (k : Nat), l.length ≤ k →
    natBits k (ofBits l) = l ++ List.replicate (k - l.length) false
  | [], k, _ => by simp [ofBits, natBits_zero]
  | b :: r, k + 1, h => by
    simp only [List.length_cons] at h
    have ih := natBits_ofBits r k (by omega)
    have e1 : ((if b then 1 else 0) + 2 * ofBits r) / 2 = ofBits r := by split <;> omega
    have e2 : (((if b then 1 else 0) + 2 * ofBits r) % 2 == 1) = b := by cases b <;> simp
    simp only [natBits, ofBits, e1, e2, ih, List.length_cons, List.cons_append,
      Nat.add_sub_add_right]
  | _ :: _, 0, h => by simp at h

theorem bitLenAux_spec : ∀ k n, n ≤ k →
    n < 2 ^ bitLenAux k n ∧ (n ≠ 0 → 0 < bitLenAux k n ∧ 2 ^ (bitLenAux k n - 1) ≤ n)
  | 0, n, h => by simp [bitLenAux]; omega
  | k + 1, n, h => by
    by_cases hn : n = 0
    · subst hn; simp [bitLenAux]
    · have ih := bitLenAux_spec k (n / 2) (by omega)
      simp only [bitLenAux, hn, if_false, Nat.add_sub_cancel]
      refine ⟨?_, fun _ => ⟨by omega, ?_⟩⟩
      · rw [Nat.pow_succ]; omega
      · by_cases h2 : n / 2 = 0
        · have : n = 1 := by omega
          subst this; simp at *
          cases k <;> simp [bitLenAux]
        · have := (ih.2 h2).2
          have hpos := (ih.2 h2).1
          have : 2 ^ bitLenAux k (n / 2) = 2 * 2 ^ (bitLenAux k (n / 2) - 1) := by
            rw [← Nat.pow_succ']; congr 1; omega
          omega

theorem lt_two_pow_bitLen (n : Nat) : n < 2 ^ bitLen n := (bitLenAux_spec n n le_rfl).1

theorem bitLen_pos {n : Nat} (h : n ≠ 0) : 0 < bitLen n := ((bitLenAux_spec n n le_rfl).2 h).1

theorem two_pow_bitLen_le {n : Nat} (h : n ≠ 0) : 2 ^ (bitLen n - 1) ≤ n :=
  ((bitLenAux_spec n n le_rfl).2 h).2

/-! ## Reading bits back -/

/-- `B` holds the list `L` starting at bit `i`. -/
def Matches (B : Array Bool) (i : Nat) (L : List Bool) : Prop :=
  ∀ j (h : j < L.length), B[i + j]? = some L[j]

theorem Matches.append {B : Array Bool} {i : Nat} {L₁ L₂ : List Bool} :
    Matches B i (L₁ ++ L₂) ↔ Matches B i L₁ ∧ Matches B (i + L₁.length) L₂ := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have := h j (by simp; omega)
      rwa [List.getElem_append_left hj] at this
    · have := h (L₁.length + j) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa [Nat.add_assoc] using this
  · rintro ⟨h1, h2⟩ j hj
    by_cases hj1 : j < L₁.length
    · rw [List.getElem_append_left hj1]; exact h1 j hj1
    · rw [List.getElem_append_right (by omega)]
      have := h2 (j - L₁.length) (by simp at hj; omega)
      rwa [show i + L₁.length + (j - L₁.length) = i + j by omega] at this

theorem Matches.cons {B : Array Bool} {i : Nat} {b : Bool} {L : List Bool} :
    Matches B i (b :: L) ↔ B[i]? = some b ∧ Matches B (i + 1) L := by
  have := @Matches.append B i [b] L
  simp only [List.singleton_append, List.length_singleton] at this
  rw [this]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by simpa using h1 0 (by simp), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun j hj => by simp at hj; subst hj; simpa using h1, h2⟩

theorem Matches.lt_size {B : Array Bool} {i : Nat} {L : List Bool} (h : Matches B i L)
    (hL : L ≠ []) : i + L.length ≤ B.size := by
  have := h (L.length - 1) (by cases L <;> simp_all)
  have : i + (L.length - 1) < B.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (by omega)] at this
    cases this
  cases L <;> simp_all <;> omega

theorem countZeros_spec (B : Array Bool) : ∀ (c k i acc : Nat),
    Matches B i (List.replicate c false ++ [true]) → c < k →
    countZeros B k i acc = some (acc + c)
  | 0, k + 1, i, acc, h, _ => by
    have := (Matches.cons.mp (by simpa using h)).1
    simp [countZeros, this]
  | c + 1, k + 1, i, acc, h, hk => by
    rw [List.replicate_succ, List.cons_append, Matches.cons] at h
    simp only [countZeros, h.1]
    rw [countZeros_spec B c k (i + 1) (acc + 1) h.2 (by omega)]
    congr 1; omega

theorem readBits_spec (B : Array Bool) : ∀ (L : List Bool) (i acc pw : Nat),
    Matches B i L → readBits B L.length i acc pw = some (acc + pw * ofBits L)
  | [], _, acc, _, _ => by simp [readBits, ofBits]
  | b :: L, i, acc, pw, h => by
    rw [Matches.cons] at h
    simp only [readBits, h.1]
    rw [readBits_spec B L (i + 1) _ _ h.2]
    congr 1
    cases b <;> simp [ofBits] <;> ring

theorem mat_ne_nil (n : Nat) : mat n ≠ [] := by
  unfold mat; split <;> simp

theorem mod_two_pow_pred {b c : Nat} (hc : 0 < c) (h1 : 2 ^ (c - 1) ≤ b) (h2 : b < 2 ^ c) :
    2 ^ (c - 1) + b % 2 ^ (c - 1) = b := by
  have : 2 ^ c = 2 * 2 ^ (c - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]; omega

theorem rub_mat_pos {B : Array Bool} {i n b c : Nat} (_hb0 : 0 < b) (hn2 : n < 2 ^ b)
    (hc0 : 0 < c) (hc1 : 2 ^ (c - 1) ≤ b) (hc2 : b < 2 ^ c)
    (h : Matches B i (List.replicate c false ++ true :: (natBits (c - 1) b ++ natBits b n))) :
    rub B i = some (n, i + (c + c + b)) := by
  have e : List.replicate c false ++ true :: (natBits (c - 1) b ++ natBits b n)
      = ((List.replicate c false ++ [true]) ++ natBits (c - 1) b) ++ natBits b n := by simp
  rw [e, Matches.append, Matches.append] at h
  obtain ⟨⟨hz, hx⟩, hv⟩ := h
  have hsz := hz.lt_size (by simp)
  simp only [List.length_append, List.length_replicate, List.length_singleton,
    natBits_length] at hx hv hsz
  have hcz := countZeros_spec B c B.size i 0 hz (by omega)
  have hrx := readBits_spec B _ _ 0 1 hx
  have hrv := readBits_spec B _ _ 0 1 hv
  rw [natBits_length, ofBits_natBits] at hrx hrv
  rw [Nat.mod_eq_of_lt hn2] at hrv
  unfold rub
  rw [hcz]
  simp only [Nat.zero_add, show (c = 0) = False from propext ⟨by omega, False.elim⟩,
    if_false]
  rw [show i + c + 1 = i + (c + 1) by omega, hrx]
  simp only [Nat.zero_add, Nat.one_mul]
  rw [mod_two_pow_pred hc0 hc1 hc2, show i + c + c = i + (c + 1 + (c - 1)) by omega, hrv]
  simp only [Nat.zero_add, Nat.one_mul, Option.some.injEq, Prod.mk.injEq, true_and]
  omega

theorem rub_mat {B : Array Bool} {i n : Nat} (h : Matches B i (mat n)) :
    rub B i = some (n, i + (mat n).length) := by
  by_cases hn : n = 0
  · subst hn
    simp only [mat, if_true] at h ⊢
    have hsz := h.lt_size (by simp)
    unfold rub
    rw [countZeros_spec B 0 B.size i 0 (by simpa using h) (by simp at hsz; omega)]
    simp
  · have hb0 : bitLen n ≠ 0 := by have := bitLen_pos hn; omega
    simp only [mat, hn, if_false] at h ⊢
    rw [rub_mat_pos (bitLen_pos hn) (lt_two_pow_bitLen n) (bitLen_pos hb0)
      (two_pow_bitLen_le hb0) (lt_two_pow_bitLen _) h]
    simp only [List.length_append, List.length_replicate, List.length_cons, natBits_length]
    have := bitLen_pos hb0
    congr 2; omega

/-! ## The jam table -/

theorem jamAux_len_pos : ∀ (n : Noun) (m : JamTable) (pos : Nat), 0 < (jamAux n m pos).1.length
  | atom x, m, pos => by
    simp only [jamAux]; split
    · split <;> simp
    · simp
  | cell _ _, m, pos => by
    simp only [jamAux]; split <;> simp

theorem jamAux_table_mono (a : Noun) (p : Nat) : ∀ (n : Noun) (m : JamTable) (pos : Nat),
    lookupPos a m = some p → lookupPos a (jamAux n m pos).2 = some p
  | atom x, m, pos, h => by
    simp only [jamAux]
    split
    · split <;> exact h
    · rename_i hn
      simp only [lookupPos]
      split
      · rename_i he; subst he; rw [hn] at h; cases h
      · exact h
  | cell hd tl, m, pos, h => by
    simp only [jamAux]
    split
    · exact h
    · rename_i hn
      apply jamAux_table_mono a p tl
      apply jamAux_table_mono a p hd
      simp only [lookupPos]
      split
      · rename_i he; subst he; rw [hn] at h; cases h
      · exact h

theorem jamAux_table_new (a : Noun) (p : Nat) : ∀ (n : Noun) (m : JamTable) (pos : Nat),
    lookupPos a (jamAux n m pos).2 = some p →
    lookupPos a m = some p ∨
      (pos ≤ p ∧ p < pos + (jamAux n m pos).1.length ∧ a.size ≤ n.size)
  | atom x, m, pos, h => by
    simp only [jamAux] at h ⊢
    split at h
    · split at h <;> exact Or.inl h
    · simp only [lookupPos] at h
      split at h
      · rename_i he; subst he; cases h; right; simp
      · exact Or.inl h
  | cell hd tl, m, pos, h => by
    simp only [jamAux] at h ⊢
    split at h
    · exact Or.inl h
    · simp only [List.length_cons, List.length_append]
      have hh := jamAux_len_pos hd ((cell hd tl, pos) :: m) (pos + 2)
      rcases jamAux_table_new a p tl _ _ h with h1 | ⟨h1, h2, h3⟩
      · rcases jamAux_table_new a p hd _ _ h1 with h4 | ⟨h4, h5, h6⟩
        · simp only [lookupPos] at h4
          split at h4
          · rename_i he; subst he; cases h4; right; simp [size]
          · exact Or.inl h4
        · right; simp only [size]; omega
      · right; simp only [size]; omega

/-! ## Decoding what jam emitted -/

theorem Matches.getElem_lt {B : Array Bool} {i : Nat} {b : Bool} {L : List Bool}
    (h : Matches B i (b :: L)) : i < B.size := by
  have := h.lt_size (by simp); simp at this; omega

theorem decode_atom {B : Array Bool} {pos x fuel : Nat} {t : CueTable}
    (h : Matches B pos (false :: mat x)) (hf : 1 ≤ fuel) :
    decode B fuel pos t =
      some (atom x, pos + (false :: mat x).length, t.setIfInBounds pos (some (atom x))) := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  rw [Matches.cons] at h
  simp only [decode, h.1, rub_mat h.2, List.length_cons]
  congr 3; omega

theorem decode_backref {B : Array Bool} {pos p fuel : Nat} {t : CueTable} {n : Noun}
    (h : Matches B pos (true :: true :: mat p)) (hp : t[p]? = some (some n)) (hf : 1 ≤ fuel) :
    decode B fuel pos t = some (n, pos + (true :: true :: mat p).length, t) := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  rw [Matches.cons, Matches.cons] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [show pos + 1 + 1 = pos + 2 by omega] at h3
  simp only [decode, h1, h2, rub_mat h3, hp, List.length_cons]
  congr 3; omega

theorem getElem?_setIfInBounds_ne {t : CueTable} {i q : Nat} {v : Option Noun} (h : i ≠ q) :
    (t.setIfInBounds i v)[q]? = t[q]? := by
  rw [Array.getElem?_setIfInBounds]; simp [h]

theorem getElem?_setIfInBounds_self {t : CueTable} {i : Nat} {v : Option Noun} (h : i < t.size) :
    (t.setIfInBounds i v)[i]? = some v := by
  rw [Array.getElem?_setIfInBounds]; simp [h]

/-- The encode/decode invariant: decoding the bits `jamAux` emitted at `pos`
returns the noun, provided every table entry of size `≤ K` is already decoded
at its position (entries of larger size are the pending ancestors, which the
subterm can never reference). -/
theorem decode_jamAux (B : Array Bool) : ∀ (n : Noun) (m : JamTable) (pos : Nat) (t : CueTable)
    (K fuel : Nat),
    Matches B pos (jamAux n m pos).1 →
    (∀ a p, lookupPos a m = some p → p < pos) →
    (∀ a p, lookupPos a m = some p → a.size ≤ K → t[p]? = some (some a)) →
    n.size ≤ K → t.size = B.size → (jamAux n m pos).1.length ≤ fuel →
    ∃ t', decode B fuel pos t = some (n, pos + (jamAux n m pos).1.length, t') ∧
      t'.size = B.size ∧ (∀ q, q < pos → t'[q]? = t[q]?) ∧
      (∀ a p, lookupPos a (jamAux n m pos).2 = some p → a.size ≤ K → t'[p]? = some (some a))
  | atom x, m, pos, t, K, fuel, hM, hlt, hinv, hK, hsz, hf => by
    simp only [jamAux] at hM hf ⊢
    split at hM
    · rename_i p hs
      simp only [hs] at hf ⊢
      split at hM
      · rename_i hle
        simp only [hle, if_true] at hf ⊢
        have hpos := hM.getElem_lt
        refine ⟨_, decode_atom hM (by simp at hf; omega), by simp [hsz], fun q hq => ?_,
          fun a p' ha haK => ?_⟩
        · exact getElem?_setIfInBounds_ne (by omega)
        · rw [getElem?_setIfInBounds_ne (by have := hlt a p' ha; omega)]; exact hinv a p' ha haK
      · rename_i hle
        simp only [hle, if_false] at hf ⊢
        exact ⟨t, decode_backref hM (hinv _ _ hs (by simp [size] at hK ⊢; omega))
          (by simp at hf; omega), hsz, fun _ _ => rfl, hinv⟩
    · rename_i hn
      simp only [hn] at hf ⊢
      have hpos := hM.getElem_lt
      refine ⟨_, decode_atom hM (by simp at hf; omega), by simp [hsz], fun q hq => ?_,
        fun a p' ha haK => ?_⟩
      · exact getElem?_setIfInBounds_ne (by omega)
      · simp only [lookupPos] at ha
        split at ha
        · rename_i he; subst he; cases ha
          exact getElem?_setIfInBounds_self (by omega)
        · rw [getElem?_setIfInBounds_ne (by have := hlt a p' ha; omega)]; exact hinv a p' ha haK
  | cell hd tl, m, pos, t, K, fuel, hM, hlt, hinv, hK, hsz, hf => by
    simp only [jamAux] at hM hf ⊢
    split at hM
    · rename_i p hs
      simp only [hs] at hf ⊢
      exact ⟨t, decode_backref hM (hinv _ _ hs hK) (by simp at hf; omega), hsz,
        fun _ _ => rfl, hinv⟩
    · rename_i hn
      simp only [hn] at hf ⊢
      -- names for the two children's emissions
      generalize hrh : jamAux hd ((cell hd tl, pos) :: m) (pos + 2) = rh at hM hf ⊢
      generalize hrt : jamAux tl rh.2 (pos + 2 + rh.1.length) = rt at hM hf ⊢
      have hpos := hM.getElem_lt
      rw [Matches.cons, Matches.cons, Matches.append] at hM
      obtain ⟨hb0, hb1, hMh, hMt⟩ := hM
      rw [show pos + 1 + 1 = pos + 2 by omega] at hMh hMt
      simp only [List.length_cons, List.length_append] at hf ⊢
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      have hSz : (cell hd tl).size = hd.size + tl.size + 1 := rfl
      -- the table after inserting the cell itself
      have hlt1 : ∀ a p, lookupPos a ((cell hd tl, pos) :: m) = some p → p < pos + 2 := by
        intro a p ha; simp only [lookupPos] at ha; split at ha
        · cases ha; omega
        · have := hlt a p ha; omega
      have hinv1 : ∀ a p, lookupPos a ((cell hd tl, pos) :: m) = some p →
          a.size ≤ hd.size + tl.size → t[p]? = some (some a) := by
        intro a p ha haK; simp only [lookupPos] at ha; split at ha
        · rename_i he; subst he; simp [size] at haK
        · exact hinv a p ha (by omega)
      obtain ⟨t1, hd1, hsz1, hbelow1, hinv1'⟩ := decode_jamAux B hd _ (pos + 2) t
        (hd.size + tl.size) k (by rw [hrh]; exact hMh) hlt1 hinv1 (by omega) hsz
        (by rw [hrh]; omega)
      rw [hrh] at hd1 hinv1'
      have hlt2 : ∀ a p, lookupPos a rh.2 = some p → p < pos + 2 + rh.1.length := by
        intro a p ha
        rw [← hrh] at ha
        rcases jamAux_table_new a p hd _ _ ha with h1 | ⟨_, h2, _⟩
        · have := hlt1 a p h1; omega
        · rw [hrh] at h2; exact h2
      obtain ⟨t2, hd2, hsz2, hbelow2, hinv2'⟩ := decode_jamAux B tl rh.2
        (pos + 2 + rh.1.length) t1 (hd.size + tl.size) k (by rw [hrt]; exact hMt) hlt2 hinv1'
        (by omega) hsz1 (by rw [hrt]; omega)
      rw [hrt] at hd2 hinv2'
      refine ⟨t2.setIfInBounds pos (some (cell hd tl)), ?_, by simp [hsz2], ?_, ?_⟩
      · simp only [decode, hb0, hb1, hd1, hd2]
        congr 3; omega
      · intro q hq
        rw [getElem?_setIfInBounds_ne (by omega), hbelow2 q (by omega), hbelow1 q (by omega)]
      · intro a p ha haK
        by_cases he : a = cell hd tl
        · subst he
          have h0 : lookupPos (cell hd tl) ((cell hd tl, pos) :: m) = some pos := by
            simp [lookupPos]
          have h1 := jamAux_table_mono _ _ hd _ (pos + 2) h0
          rw [hrh] at h1
          have h2 := jamAux_table_mono _ _ tl _ (pos + 2 + rh.1.length) h1
          rw [hrt, ha] at h2
          cases h2
          exact getElem?_setIfInBounds_self (by omega)
        · -- where did `a` enter the table?
          have hrt' := hrt ▸ ha
          rcases jamAux_table_new a p tl _ _ (hrt ▸ ha) with h1 | ⟨h1, h2, h3⟩
          · rw [← hrh] at h1
            rcases jamAux_table_new a p hd _ _ h1 with h4 | ⟨h4, h5, h6⟩
            · simp only [lookupPos, he, if_false] at h4
              have hp := hlt a p h4
              rw [getElem?_setIfInBounds_ne (by omega), hbelow2 p (by omega),
                hbelow1 p (by omega)]
              exact hinv a p h4 haK
            · rw [getElem?_setIfInBounds_ne (by omega)]
              exact hinv2' a p (hrt ▸ ha) (by omega)
          · rw [getElem?_setIfInBounds_ne (by omega)]
            exact hinv2' a p (hrt ▸ ha) (by omega)

/-! ## Bytes -/

theorem toUInt8_toNat_of_lt {x : Nat} (h : x < 256) : x.toUInt8.toNat = x := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt h]

theorem fromBytes_toBytesAux : ∀ (k : Nat) (bs : List Bool), bs.length ≤ 8 * k →
    ∃ r, fromBytes (toBytesAux k bs) = bs ++ List.replicate r false
  | 0, bs, h => ⟨0, by
      have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; rfl⟩
  | k + 1, bs, h => by
    by_cases hb : bs = []
    · subst hb; exact ⟨0, by simp [toBytesAux, fromBytes]⟩
    · have hlt : ofBits (bs.take 8) < 256 := by
        have := ofBits_lt (bs.take 8)
        have h8 : (bs.take 8).length ≤ 8 := by simp
        calc ofBits (bs.take 8) < 2 ^ (bs.take 8).length := this
          _ ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) h8
      obtain ⟨r, hr⟩ := fromBytes_toBytesAux k (bs.drop 8) (by simp; omega)
      simp only [toBytesAux, hb, if_false, fromBytes, toUInt8_toNat_of_lt hlt]
      rw [natBits_ofBits _ _ (by simp), hr]
      by_cases h8 : bs.length ≤ 8
      · have hd : bs.drop 8 = [] := List.drop_eq_nil_of_le h8
        rw [hd, List.take_of_length_le h8]
        exact ⟨8 - bs.length + r, by rw [List.append_assoc, List.nil_append, List.replicate_append_replicate]⟩
      · have ht : (bs.take 8).length = 8 := by simp; omega
        refine ⟨r, ?_⟩
        rw [ht, Nat.sub_self, List.replicate_zero, List.append_nil, ← List.append_assoc,
          List.take_append_drop]

theorem fromBytes_toBytes (bs : List Bool) :
    ∃ r, fromBytes (toBytes bs) = bs ++ List.replicate r false :=
  fromBytes_toBytesAux _ _ (by omega)

theorem Matches.of_toList {B : Array Bool} {L R : List Bool} (h : B.toList = L ++ R) :
    Matches B 0 L := by
  intro j hj
  rw [← Array.getElem?_toList, h, Nat.zero_add, List.getElem?_append_left hj,
    List.getElem?_eq_getElem hj]

/-! ## The round trip -/

/-- **cue ∘ jam = id**: Hoon's codec, back-references included, decodes what it
encodes. -/
theorem cue_jam (n : Noun) : cue (jam n) = some n := by
  obtain ⟨r, hr⟩ := fromBytes_toBytes (jamBits n)
  unfold cue jam
  simp only [hr]
  have hM : Matches (jamBits n ++ List.replicate r false).toArray 0 (jamAux n [] 0).1 :=
    Matches.of_toList (R := List.replicate r false) (by simp [jamBits])
  obtain ⟨t', hdec, -⟩ := decode_jamAux _ n [] 0
    (Array.replicate (jamBits n ++ List.replicate r false).toArray.size none) n.size
    (jamBits n ++ List.replicate r false).toArray.size hM
    (by intro a p h; simp [lookupPos] at h) (by intro a p h; simp [lookupPos] at h) le_rfl
    (by simp) (by simp [jamBits])
  rw [hdec]

/-- `jam` is injective: distinct nouns have distinct jams. -/
theorem jam_injective {a b : Noun} (h : jam a = jam b) : a = b := by
  have := cue_jam a
  rw [h, cue_jam b] at this
  exact (Option.some.inj this).symm

/-- `jam` output is canonical. -/
theorem canonical_jam (n : Noun) : canonical (jam n) = true := by
  simp [canonical, cue_jam]

/-- Two canonical byte strings that cue to the same noun are equal: the
content address of a canonical jam is a function of the noun. -/
theorem canonical_unique {bs bs' : List UInt8} (h : canonical bs = true)
    (h' : canonical bs' = true) (he : cue bs = cue bs') : bs = bs' := by
  simp only [canonical] at h h'
  cases hc : cue bs with
  | none => rw [hc] at h; simp at h
  | some n =>
    rw [hc] at h he
    rw [← he] at h'
    simp at h h'
    rw [← h, ← h']

theorem canonical_iff {bs : List UInt8} : canonical bs = true ↔ ∃ n, jam n = bs := by
  constructor
  · intro h
    simp only [canonical] at h
    cases hc : cue bs with
    | none => rw [hc] at h; simp at h
    | some n => rw [hc] at h; simp at h; exact ⟨n, h⟩
  · rintro ⟨n, rfl⟩; exact canonical_jam n

theorem toNoun_injective {a b : Int} (h : a.toNoun = b.toNoun) : a = b := by
  cases a <;> cases b <;> simp [Int.toNoun] at h <;> first | (subst h; rfl) | omega

theorem toInt?_toNoun (z : Int) : z.toNoun.toInt? = some z := by
  cases z with
  | ofNat n => simp [Int.toNoun, toInt?]
  | negSucc n =>
    simp only [Int.toNoun, toInt?]
    have h1 : (2 * n + 1) % 2 = 1 := by omega
    have h2 : (2 * n + 1) / 2 = n := by omega
    simp [h1, h2]

/-! ## Poles

Values from Hoon's documentation of `++jam` (`(jam 0) = 2`, `(jam 1) = 12`,
`(jam [0 0]) = 41`, `(jam [1 1]) = 817`), the repository's own test jam, and
nockvm's cyclic-backref regression (`serialization.rs`, GHSA-vv3m-g96f-73r4).
Byte-equality with `nockvm`'s `jam` on the large corpus files and on random
nouns is the differential harness's job (NOCK-RUNNER, J-NOCK-1a). -/

theorem jam_atom_zero : jam (atom 0) = [0x02] := by decide
theorem jam_atom_one : jam (atom 1) = [0x0c] := by decide
theorem jam_cell_zero_zero : jam (cell (atom 0) (atom 0)) = [0x29] := by decide
theorem jam_cell_one_one : jam (cell (atom 1) (atom 1)) = [0x31, 0x03] := by decide

/-- A shared subtree is emitted once and back-referenced: `[[5 5] [5 5]]`
jams to 4 bytes (the tail `[5 5]` is `11` + a reference to bit 2). -/
theorem jam_shared : jam (cell (cell (atom 5) (atom 5)) (cell (atom 5) (atom 5))) =
    [133, 139, 59, 9] := by decide

/-- `nockchain@cbd9298f:hoon/test-jams/cue-test.jam` is the two bytes `31 0a`. It
cues to `[1 1]` — with a non-minimal length prefix on the second `1` — so it is
NOT canonical: its re-jam is `31 03`. -/
theorem cue_test_jam : cue [0x31, 0x0a] = some (cell (atom 1) (atom 1)) := by decide
theorem cue_test_jam_not_canonical : canonical [0x31, 0x0a] = false := by decide

/-- `0x5D`: a cell whose head back-references the cell itself. Refused, as in
Hoon's `++cue` (a cell's entry is registered only after both children). -/
theorem cue_self_reference_refused : cue [0x5D] = none := by decide
theorem cue_empty_refused : cue [] = none := by decide
/-- A cell tag with nothing after it: a read past the end. -/
theorem cue_truncated_refused : cue [0x01] = none := by decide

theorem axis_one (n : Noun) : axis 1 n = some n := by simp [axis, axisAux]
theorem axis_zero (n : Noun) : axis 0 n = none := by simp [axis, axisAux]
theorem axis_seven : axis 7 (cell (atom 1) (cell (atom 2) (atom 3))) = some (atom 3) := by decide
theorem axis_into_atom_refused : axis 2 (atom 5) = none := by decide
theorem edit_two : edit 2 (atom 9) (cell (atom 1) (atom 2)) = some (cell (atom 9) (atom 2)) := by
  decide
theorem edit_six :
    edit 6 (atom 9) (cell (atom 1) (cell (atom 2) (atom 3))) =
      some (cell (atom 1) (cell (atom 9) (atom 3))) := by decide
theorem edit_zero_refused : edit 0 (atom 9) (atom 1) = none := by decide
theorem edit_into_atom_refused : edit 2 (atom 9) (atom 1) = none := by decide


/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.Noun.natBits_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms natBits_length
/-- info: 'Minidregg.Theory.Noun.ofBits_natBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ofBits_natBits
/-- info: 'Minidregg.Theory.Noun.ofBits_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms ofBits_append
/-- info: 'Minidregg.Theory.Noun.ofBits_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ofBits_lt
/-- info: 'Minidregg.Theory.Noun.natBits_ofBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms natBits_ofBits
/-- info: 'Minidregg.Theory.Noun.lt_two_pow_bitLen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lt_two_pow_bitLen
/-- info: 'Minidregg.Theory.Noun.two_pow_bitLen_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms two_pow_bitLen_le
/-- info: 'Minidregg.Theory.Noun.rub_mat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rub_mat
/-- info: 'Minidregg.Theory.Noun.jamAux_table_mono' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms jamAux_table_mono
/-- info: 'Minidregg.Theory.Noun.jamAux_table_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms jamAux_table_new
/-- info: 'Minidregg.Theory.Noun.decode_jamAux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decode_jamAux
/-- info: 'Minidregg.Theory.Noun.fromBytes_toBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fromBytes_toBytes
/-- info: 'Minidregg.Theory.Noun.cue_jam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cue_jam
/-- info: 'Minidregg.Theory.Noun.jam_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms jam_injective
/-- info: 'Minidregg.Theory.Noun.canonical_jam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonical_jam
/-- info: 'Minidregg.Theory.Noun.canonical_unique' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms canonical_unique
/-- info: 'Minidregg.Theory.Noun.canonical_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonical_iff
/-- info: 'Minidregg.Theory.Noun.toNoun_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toNoun_injective
/-- info: 'Minidregg.Theory.Noun.toInt?_toNoun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toInt?_toNoun
/-- info: 'Minidregg.Theory.Noun.jam_atom_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms jam_atom_zero
/-- info: 'Minidregg.Theory.Noun.jam_atom_one' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms jam_atom_one
/-- info: 'Minidregg.Theory.Noun.jam_cell_zero_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms jam_cell_zero_zero
/-- info: 'Minidregg.Theory.Noun.jam_cell_one_one' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms jam_cell_one_one
/-- info: 'Minidregg.Theory.Noun.jam_shared' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms jam_shared
/-- info: 'Minidregg.Theory.Noun.cue_test_jam' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms cue_test_jam
/-- info: 'Minidregg.Theory.Noun.cue_test_jam_not_canonical' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms cue_test_jam_not_canonical
/-- info: 'Minidregg.Theory.Noun.cue_self_reference_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms cue_self_reference_refused
/-- info: 'Minidregg.Theory.Noun.cue_empty_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms cue_empty_refused
/-- info: 'Minidregg.Theory.Noun.cue_truncated_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms cue_truncated_refused
/-- info: 'Minidregg.Theory.Noun.axis_one' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms axis_one
/-- info: 'Minidregg.Theory.Noun.axis_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms axis_zero
/-- info: 'Minidregg.Theory.Noun.axis_seven' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms axis_seven
/-- info: 'Minidregg.Theory.Noun.axis_into_atom_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms axis_into_atom_refused
/-- info: 'Minidregg.Theory.Noun.edit_two' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms edit_two
/-- info: 'Minidregg.Theory.Noun.edit_six' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms edit_six
/-- info: 'Minidregg.Theory.Noun.edit_zero_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms edit_zero_refused
/-- info: 'Minidregg.Theory.Noun.edit_into_atom_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms edit_into_atom_refused

end Noun
end Minidregg.Theory
