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

Every specification function here is structurally recursive, so small
instances evaluate by `decide` in the kernel.

Runtime shape (nockvm's `mug`): every noun carries a 64-bit structural hash
`mug`, a Lean computed field stored in the constructor and computed once when
the node is built, so nouns shared by pointer (as `cue` builds them) hash in
O(1) per node. Logically `mug` is an ordinary recursive function and `Noun` is
the plain inductive; the kernel never evaluates a hash. Two `@[csimp]`
theorems swap the specification functions for the fast ones in compiled code:
`decEq_eq_decEqFast` (pointer equality, then `mug`, then structure; this is
Nock `%5`'s equality) and `jam_eq_jamFast` (the back-reference table is a
`Std.HashMap` keyed by `mug`, proved to answer exactly as `lookupPos`).
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

namespace Minidregg.Theory

/-- A Nock noun: an atom (any natural) or a cell. `mug` is cached per node. -/
inductive Noun where
  | atom (n : Nat)
  | cell (h t : Noun)
with
  /-- The structural hash (nockvm's `mug`, not its values): stored in each
  constructor at runtime, so reading it is O(1). -/
  @[computed_field] mug : Noun → UInt64
  | .atom n => hash n
  | .cell h t => mixHash (mug h) (mug t)
  deriving Repr, Inhabited

namespace Noun

/-! ## Equality: the structural specification and the mug-first runtime check -/

/-- Structural equality, the specification (`%5`, `lookupPos`). -/
def decEq : (a b : Noun) → Decidable (a = b)
  | atom x, atom y =>
    if h : x = y then isTrue (congrArg atom h) else isFalse (fun e => h (Noun.atom.inj e))
  | atom _, cell _ _ => isFalse (fun e => Noun.noConfusion e)
  | cell _ _, atom _ => isFalse (fun e => Noun.noConfusion e)
  | cell h t, cell h' t' =>
    match decEq h h' with
    | isFalse n => isFalse (fun e => n (Noun.cell.inj e).1)
    | isTrue e1 =>
      match decEq t t' with
      | isFalse n => isFalse (fun e => n (Noun.cell.inj e).2)
      | isTrue e2 => isTrue (e1 ▸ e2 ▸ rfl)

/-- The runtime equality: equal pointers are equal; unequal mugs are unequal;
only on a mug match is the structure compared (children first by pointer). -/
def decEqFast (a b : Noun) : Decidable (a = b) :=
  withPtrEqDecEq a b fun _ =>
    if hm : a.mug = b.mug then
      match a, b with
      | atom x, atom y =>
        if h : x = y then isTrue (congrArg atom h) else isFalse (fun e => h (Noun.atom.inj e))
      | atom _, cell _ _ => isFalse (fun e => Noun.noConfusion e)
      | cell _ _, atom _ => isFalse (fun e => Noun.noConfusion e)
      | cell h t, cell h' t' =>
        match decEqFast h h' with
        | isFalse n => isFalse (fun e => n (Noun.cell.inj e).1)
        | isTrue e1 =>
          match decEqFast t t' with
          | isFalse n => isFalse (fun e => n (Noun.cell.inj e).2)
          | isTrue e2 => isTrue (e1 ▸ e2 ▸ rfl)
    else isFalse (fun e => hm (congrArg mug e))

/-- Compiled code decides `Noun` equality by `decEqFast` (a `Decidable` is a
subsingleton, so the two agree on every input). -/
@[csimp] theorem decEq_eq_decEqFast : @decEq = @decEqFast := by
  funext a b; exact Subsingleton.elim _ _

/-- Declared after `decEq_eq_decEqFast`: code that inlines this instance is
compiled with the replacement in force. -/
instance : DecidableEq Noun := decEq

/-- Mug equality is necessary for equality; structural equality decides it. -/
theorem eq_iff_mugEq_and_structEq {a b : Noun} :
    a = b ↔ a.mug = b.mug ∧ decide (a = b) = true :=
  ⟨fun e => ⟨congrArg mug e, decide_eq_true e⟩, fun h => of_decide_eq_true h.2⟩

theorem ne_of_mug_ne {a b : Noun} (h : a.mug ≠ b.mug) : a ≠ b :=
  fun e => h (congrArg mug e)

instance : Hashable Noun := ⟨mug⟩

instance : LawfulHashable Noun where
  hash_eq {a b} h := by rw [eq_of_beq h]

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

/-! ## Fast bit primitives

`bitLen` walks the atom one bit at a time and `natBits` halves it once per bit:
both are quadratic in the atom's length (a 64 KB atom re-jammed in 52 s and
48 GB). Compiled code runs `bitLenFast` (`Nat.log2`) and `natBitsFast` (split
in halves by mask and shift), proved equal. -/

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

def bitLenFast (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

@[csimp] theorem bitLen_eq_bitLenFast : @bitLen = @bitLenFast := by
  funext n
  have hs := bitLenAux_spec n n le_rfl
  unfold bitLenFast
  split
  · rename_i hn; subst hn; rfl
  · rename_i hn
    have h1 : n < 2 ^ bitLen n := hs.1
    have h2 := (hs.2 hn).1
    have h3 : 2 ^ (bitLen n - 1) ≤ n := (hs.2 hn).2
    have a := (Nat.log2_lt hn).2 h1
    have b := (Nat.le_log2 hn).2 h3
    omega

/-- `natBits`, restated for the base case of `natBitsFast`. -/
def natBitsLoop : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, n => (n % 2 == 1) :: natBitsLoop k (n / 2)

theorem natBitsLoop_eq : ∀ k n, natBitsLoop k n = natBits k n
  | 0, _ => rfl
  | k + 1, n => by simp [natBitsLoop, natBits, natBitsLoop_eq k]

theorem natBits_add : ∀ (a b n : Nat), natBits (a + b) n = natBits a n ++ natBits b (n / 2 ^ a)
  | 0, b, n => by simp [natBits]
  | a + 1, b, n => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [natBits, natBits_add a b (n / 2), List.cons_append, Nat.div_div_eq_div_mul,
      Nat.pow_succ']

theorem natBits_mod : ∀ (a n : Nat), natBits a (n % 2 ^ a) = natBits a n
  | 0, _ => rfl
  | a + 1, n => by
    simp only [natBits]
    rw [Nat.pow_succ', Nat.mod_mul_right_div_self, natBits_mod a (n / 2),
      Nat.mod_mod_of_dvd n (Dvd.intro (2 ^ a) rfl)]

/-- The low `k` bits of `n` by halving `k`: `O(k log k)` word operations. -/
def natBitsFast (k n : Nat) : List Bool :=
  if k ≤ 64 then natBitsLoop k n
  else natBitsFast (k / 2) (n &&& (2 ^ (k / 2) - 1)) ++ natBitsFast (k - k / 2) (n >>> (k / 2))
termination_by k
decreasing_by all_goals omega

@[csimp] theorem natBits_eq_natBitsFast : @natBits = @natBitsFast := by
  funext k n
  induction k using Nat.strong_induction_on generalizing n with
  | _ k ih =>
    rw [natBitsFast]
    split
    · exact (natBitsLoop_eq k n).symm
    · rw [← ih _ (by omega), ← ih _ (by omega), Nat.and_two_pow_sub_one_eq_mod, natBits_mod,
        Nat.shiftRight_eq_div_pow, ← natBits_add]
      congr 1; omega

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

theorem rub_mat_pos {B : Array Bool} {i n b c : Nat} (hn2 : n < 2 ^ b)
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
    rw [rub_mat_pos (lt_two_pow_bitLen n) (bitLen_pos hb0)
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

/-! ## The fast cue: a byte-indexed reader and a position-keyed hash table

`cue` materialises one `Bool` per bit and a table slot per bit (about 500 bytes
of heap per input byte). Compiled code runs `cueFast`: bits are read from the
bytes in place, the table holds only positions where a noun started, and atom
values are read by halving (`readVal`), so a large atom is `O(b log b)`, not
quadratic. `cue_eq_cueFast` proves the two equal. -/

/-- Bit `i` of a byte array, byte 0 bit 0 first. -/
def getBit (D : ByteArray) (i : Nat) : Option Bool :=
  if h : i / 8 < D.size then some ((D[i / 8].toNat >>> (i % 8)) % 2 == 1) else none

theorem getElem?_natBits : ∀ (k n j : Nat),
    (natBits k n)[j]? = if j < k then some (n / 2 ^ j % 2 == 1) else none
  | 0, n, j => by simp [natBits]
  | k + 1, n, 0 => by simp [natBits]
  | k + 1, n, j + 1 => by
    simp only [natBits, List.getElem?_cons_succ, getElem?_natBits k (n / 2) j,
      Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    simp

theorem length_fromBytes : ∀ bs : List UInt8, (fromBytes bs).length = 8 * bs.length
  | [] => rfl
  | b :: r => by
    simp [fromBytes, natBits_length, length_fromBytes r]; ring

theorem getElem?_fromBytes : ∀ (bs : List UInt8) (i : Nat),
    (fromBytes bs)[i]? =
      if h : i / 8 < bs.length then some (bs[i / 8].toNat / 2 ^ (i % 8) % 2 == 1) else none
  | [], i => by simp [fromBytes]
  | b :: r, i => by
    have hl : (natBits 8 b.toNat).length = 8 := by simp [natBits]
    simp only [fromBytes]
    by_cases hi : i < 8
    · rw [List.getElem?_append_left (by omega), getElem?_natBits]
      have h0 : i / 8 = 0 := Nat.div_eq_of_lt hi
      have h1 : i % 8 = i := Nat.mod_eq_of_lt hi
      simp [hi, h0, h1]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 8 := ⟨i - 8, by omega⟩
      rw [List.getElem?_append_right (by omega), hl, Nat.add_sub_cancel, getElem?_fromBytes r j]
      have h0 : (j + 8) / 8 = j / 8 + 1 := Nat.add_div_right j (by omega)
      have h1 : (j + 8) % 8 = j % 8 := Nat.add_mod_right j 8
      simp only [h0, h1, List.length_cons, Nat.add_lt_add_iff_right, List.getElem_cons_succ]

theorem getBit_eq (bs : List UInt8) (i : Nat) :
    getBit ⟨bs.toArray⟩ i = (fromBytes bs).toArray[i]? := by
  rw [List.getElem?_toArray, getElem?_fromBytes, getBit]
  by_cases h : i / 8 < bs.length
  · have h' : i / 8 < (⟨bs.toArray⟩ : ByteArray).size := h
    rw [dif_pos h', dif_pos h, Nat.shiftRight_eq_div_pow]; rfl
  · have h' : ¬ i / 8 < (⟨bs.toArray⟩ : ByteArray).size := h
    rw [dif_neg h', dif_neg h]

def countZerosF (g : Nat → Option Bool) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | k + 1, i, c =>
    match g i with
    | none => none
    | some true => some c
    | some false => countZerosF g k (i + 1) (c + 1)

theorem countZerosF_eq {B : Array Bool} {g : Nat → Option Bool} (hg : ∀ i, g i = B[i]?) :
    ∀ k i c, countZerosF g k i c = countZeros B k i c
  | 0, _, _ => rfl
  | k + 1, i, c => by
    simp only [countZerosF, countZeros, hg i]
    cases B[i]? with
    | none => rfl
    | some b => cases b <;> simp [countZerosF_eq hg k]

/-- `l` bits from position `i`, little-endian, one at a time. -/
def readValLoop (g : Nat → Option Bool) : Nat → Nat → Option Nat
  | 0, _ => some 0
  | l + 1, i =>
    match g i with
    | none => none
    | some b => (readValLoop g l (i + 1)).map fun v => (if b then 1 else 0) + 2 * v

theorem readBits_eq_loop {B : Array Bool} {g : Nat → Option Bool} (hg : ∀ i, g i = B[i]?) :
    ∀ l i acc pw, readBits B l i acc pw = (readValLoop g l i).map fun v => acc + pw * v
  | 0, _, _, _ => by simp [readBits, readValLoop]
  | l + 1, i, acc, pw => by
    simp only [readBits, readValLoop, hg i]
    cases B[i]? with
    | none => rfl
    | some b =>
      simp only [readBits_eq_loop hg l, Option.map_map]
      congr 1; funext v; cases b <;> simp <;> ring

theorem readValLoop_add (g : Nat → Option Bool) : ∀ a b i, readValLoop g (a + b) i =
    (readValLoop g a i).bind fun v₁ => (readValLoop g b (i + a)).map fun v₂ => v₁ + 2 ^ a * v₂
  | 0, b, i => by simp [readValLoop]
  | a + 1, b, i => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [readValLoop]
    cases g i with
    | none => rfl
    | some c =>
      simp only [readValLoop_add g a b (i + 1), show i + 1 + a = i + (a + 1) by omega]
      cases readValLoop g a (i + 1) with
      | none => rfl
      | some v₁ =>
        cases readValLoop g b (i + (a + 1)) with
        | none => rfl
        | some v₂ => simp only [Option.bind_some, Option.map_some]; congr 1; rw [Nat.pow_succ]; ring

/-- `readValLoop` by halving the width: `O(l log l)` word operations. -/
def readVal (g : Nat → Option Bool) (l i : Nat) : Option Nat :=
  if l ≤ 64 then readValLoop g l i
  else
    match readVal g (l / 2) i with
    | none => none
    | some v₁ =>
      match readVal g (l - l / 2) (i + l / 2) with
      | none => none
      | some v₂ => some (v₁ + (v₂ <<< (l / 2)))
termination_by l
decreasing_by all_goals omega

theorem readVal_eq (g : Nat → Option Bool) (l i : Nat) : readVal g l i = readValLoop g l i := by
  induction l using Nat.strong_induction_on generalizing i with
  | _ l ih =>
    rw [readVal]
    split
    · rfl
    · rw [ih _ (by omega), ih _ (by omega),
        show readValLoop g l i = readValLoop g (l / 2 + (l - l / 2)) i by congr 1; omega,
        readValLoop_add]
      cases readValLoop g (l / 2) i with
      | none => rfl
      | some v₁ =>
        cases readValLoop g (l - l / 2) (i + l / 2) with
        | none => rfl
        | some v₂ => simp [Nat.shiftLeft_eq, Nat.mul_comm]

/-- `rub` over a bit reader of `lim` bits. -/
def rubF (g : Nat → Option Bool) (lim i : Nat) : Option (Nat × Nat) :=
  match countZerosF g lim i 0 with
  | none => none
  | some c =>
    if c = 0 then some (0, i + 1)
    else
      match readVal g (c - 1) (i + c + 1) with
      | none => none
      | some x =>
        let b := 2 ^ (c - 1) + x
        match readVal g b (i + c + c) with
        | none => none
        | some v => some (v, i + c + c + b)

theorem rubF_eq {B : Array Bool} {g : Nat → Option Bool} (hg : ∀ i, g i = B[i]?) (i : Nat) :
    rubF g B.size i = rub B i := by
  simp only [rubF, rub, countZerosF_eq hg, readVal_eq, readBits_eq_loop hg]
  cases countZeros B B.size i 0 with
  | none => rfl
  | some c =>
    simp only
    split
    · rfl
    · cases readValLoop g (c - 1) (i + c + 1) with
      | none => rfl
      | some x =>
        simp only [Option.map_some, Nat.zero_add, Nat.one_mul]
        cases readValLoop g (2 ^ (c - 1) + x) (i + c + c) with
        | none => rfl
        | some v => rfl

abbrev FastCue := Std.HashMap Nat Noun

/-- `decode` over a bit reader of `lim` bits, the table keyed by start position. -/
def decodeF (g : Nat → Option Bool) (lim : Nat) : Nat → Nat → FastCue → Option (Noun × Nat × FastCue)
  | 0, _, _ => none
  | k + 1, i, M =>
    match g i with
    | none => none
    | some false =>
      match rubF g lim (i + 1) with
      | none => none
      | some (v, j) => let n := atom v; some (n, j, M.insert i n)
    | some true =>
      match g (i + 1) with
      | none => none
      | some false =>
        match decodeF g lim k (i + 2) M with
        | none => none
        | some (h, j, M1) =>
          match decodeF g lim k j M1 with
          | none => none
          | some (tl, j2, M2) => let n := cell h tl; some (n, j2, M2.insert i n)
      | some true =>
        match rubF g lim (i + 2) with
        | none => none
        | some (p, j) =>
          match M[p]? with
          | some n => some (n, j, M)
          | none => none

/-- The array table and the hash table agree on every completed position. -/
def CueRel (B : Array Bool) (t : CueTable) (M : FastCue) : Prop :=
  t.size = B.size ∧ ∀ p : Nat, (t[p]? : Option (Option Noun)).bind id = M[p]?

theorem CueRel.insert {B : Array Bool} {t : CueTable} {M : FastCue} (hR : CueRel B t M)
    {i : Nat} (hi : i < B.size) (n : Noun) :
    CueRel B (t.setIfInBounds i (some n)) (M.insert i n) := by
  refine ⟨by simp [hR.1], fun p => ?_⟩
  rw [Array.getElem?_setIfInBounds, Std.HashMap.getElem?_insert, ← hR.2 p]
  by_cases h : i = p
  · subst h; simp [hR.1, hi]
  · simp [h]

theorem decodeF_rel {B : Array Bool} {g : Nat → Option Bool} (hg : ∀ i, g i = B[i]?) :
    ∀ fuel i t M, CueRel B t M →
    Option.Rel (fun r r' => r.1 = r'.1 ∧ r.2.1 = r'.2.1 ∧ CueRel B r.2.2 r'.2.2)
      (decode B fuel i t) (decodeF g B.size fuel i M)
  | 0, _, _, _, _ => .none
  | k + 1, i, t, M, hR => by
    simp only [decode, decodeF, hg i, rubF_eq hg]
    cases hb : B[i]? with
    | none => exact .none
    | some b =>
      have hi : i < B.size := by
        rcases Nat.lt_or_ge i B.size with h | h
        · exact h
        · simp [Array.getElem?_eq_none h] at hb
      cases b with
      | false =>
        cases rub B (i + 1) with
        | none => exact .none
        | some r => exact .some ⟨rfl, rfl, hR.insert hi _⟩
      | true =>
        simp only [hg (i + 1)]
        cases B[i + 1]? with
        | none => exact .none
        | some c =>
          cases c with
          | false =>
            dsimp only
            have h1 := decodeF_rel hg k (i + 2) t M hR
            revert h1
            generalize decode B k (i + 2) t = x
            generalize decodeF g B.size k (i + 2) M = y
            intro h1
            cases h1 with
            | none => exact .none
            | @some r r' hr =>
              obtain ⟨hn, hj, hR1⟩ := hr
              obtain ⟨h, j, t1⟩ := r
              obtain ⟨h', j', M1⟩ := r'
              simp only at hn hj hR1; subst hn hj
              dsimp only
              have h2 := decodeF_rel hg k j t1 M1 hR1
              revert h2
              generalize decode B k j t1 = x
              generalize decodeF g B.size k j M1 = y
              intro h2
              cases h2 with
              | none => exact .none
              | @some s s' hs =>
                obtain ⟨hn2, hj2, hR2⟩ := hs
                obtain ⟨tl, j2, t2⟩ := s
                obtain ⟨tl', j2', M2⟩ := s'
                simp only at hn2 hj2 hR2; subst hn2 hj2
                dsimp only
                exact .some ⟨rfl, rfl, hR2.insert hi _⟩
          | true =>
            cases rub B (i + 2) with
            | none => exact .none
            | some r =>
              obtain ⟨p, j⟩ := r
              simp only
              have hp := hR.2 p
              cases htp : t[p]? with
              | none =>
                rw [htp] at hp; simp only [Option.bind_none] at hp; rw [← hp]; exact .none
              | some o =>
                rw [htp] at hp; simp only [Option.bind_some, id] at hp; rw [← hp]
                cases o with
                | none => exact .none
                | some n => exact .some ⟨rfl, rfl, hR⟩

/-- `cue` through the byte reader and the hash table. -/
def cueFast (bs : List UInt8) : Option Noun :=
  let D : ByteArray := ⟨bs.toArray⟩
  match decodeF (getBit D) (8 * D.size) (8 * D.size) 0 ∅ with
  | none => none
  | some (n, _, _) => some n

/-- Compiled code runs `cueFast` for `cue`. -/
@[csimp] theorem cue_eq_cueFast : @cue = @cueFast := by
  funext bs
  have hsz : (fromBytes bs).toArray.size = 8 * (⟨bs.toArray⟩ : ByteArray).size := by
    simp [length_fromBytes, ByteArray.size]
  have hR : CueRel (fromBytes bs).toArray
      (Array.replicate (fromBytes bs).toArray.size none) (∅ : FastCue) := by
    refine ⟨by simp, fun p => ?_⟩
    rw [Std.HashMap.getElem?_empty]
    simp [Array.getElem?_replicate]
  have h := decodeF_rel (getBit_eq bs) (fromBytes bs).toArray.size 0 _ _ hR
  simp only [cue, cueFast]
  rw [← hsz]
  revert h
  generalize decode _ _ 0 _ = x
  generalize decodeF _ _ _ 0 ∅ = y
  intro h
  cases h with
  | none => rfl
  | @some r r' hr =>
    obtain ⟨hn, -, -⟩ := hr
    obtain ⟨n, _, _⟩ := r
    obtain ⟨n', _, _⟩ := r'
    simp only at hn; subst hn; rfl

/-! ## The fast jam: a mug-keyed hash table, proved to answer as `lookupPos` -/

abbrev FastTable := Std.HashMap Noun Nat

theorem fastTable_insert {M : FastTable} {m : JamTable} (hM : ∀ a, M[a]? = lookupPos a m)
    (k : Noun) (v : Nat) : ∀ a, (M.insert k v)[a]? = lookupPos a ((k, v) :: m) := by
  intro a
  rw [Std.HashMap.getElem?_insert, hM a]
  simp only [lookupPos, beq_iff_eq]
  by_cases h : a = k
  · subst h; simp
  · simp [h, Ne.symm h]

/-- A bit writer: completed bytes, and a partial byte `cur` holding `k < 8` bits. -/
structure BitW where
  done : Array UInt8
  cur : Nat
  k : Nat

namespace BitW

/-- The bits written so far. -/
def bits (w : BitW) : List Bool := fromBytes w.done.toList ++ natBits w.k w.cur

def Inv (w : BitW) : Prop := w.k < 8 ∧ w.cur < 2 ^ w.k

def push (w : BitW) (b : Bool) : BitW :=
  let c := w.cur + (if b then 2 ^ w.k else 0)
  if w.k = 7 then ⟨w.done.push c.toUInt8, 0, 0⟩ else ⟨w.done, c, w.k + 1⟩

def pushAll (w : BitW) : List Bool → BitW
  | [] => w
  | b :: bs => (w.push b).pushAll bs

/-- The bytes, the partial byte zero-padded. -/
def finish (w : BitW) : List UInt8 :=
  if w.k = 0 then w.done.toList else w.done.toList ++ [w.cur.toUInt8]

end BitW

theorem natBits_snoc {k c : Nat} (hc : c < 2 ^ k) (b : Bool) :
    natBits (k + 1) (c + (if b then 2 ^ k else 0)) = natBits k c ++ [b] := by
  rw [natBits_add k 1, ← natBits_mod k]
  have hp := Nat.two_pow_pos k
  cases b
  · simp [Nat.mod_eq_of_lt hc, Nat.div_eq_of_lt hc, natBits]
  · simp only [if_true, Nat.add_mod_right, Nat.mod_eq_of_lt hc]
    rw [Nat.add_div_right c hp, Nat.div_eq_of_lt hc]
    simp [natBits]

theorem fromBytes_append : ∀ (L R : List UInt8), fromBytes (L ++ R) = fromBytes L ++ fromBytes R
  | [], _ => rfl
  | b :: L, R => by simp [fromBytes, fromBytes_append L R]

theorem BitW.push_spec {w : BitW} (hw : w.Inv) (b : Bool) :
    (w.push b).bits = w.bits ++ [b] ∧ (w.push b).Inv := by
  obtain ⟨hk, hc⟩ := hw
  have hs := natBits_snoc hc b
  have hlt : w.cur + (if b then 2 ^ w.k else 0) < 2 ^ (w.k + 1) := by
    rw [Nat.pow_succ]; cases b <;> simp <;> omega
  have hp : w.push b = if w.k = 7 then ⟨w.done.push (w.cur + (if b then 2 ^ w.k else 0)).toUInt8, 0, 0⟩
      else ⟨w.done, w.cur + (if b then 2 ^ w.k else 0), w.k + 1⟩ := rfl
  generalize w.cur + (if b then 2 ^ w.k else 0) = x at hs hlt hp
  rw [hp]
  by_cases h7 : w.k = 7
  · rw [if_pos h7]
    rw [h7] at hs hlt
    have hs8 : natBits 8 x = natBits 7 w.cur ++ [b] := hs
    refine ⟨?_, by simp [Inv]⟩
    simp only [bits, Array.toList_push, fromBytes_append, fromBytes, List.append_nil, h7]
    rw [toUInt8_toNat_of_lt (by simpa using hlt), hs8]
    simp [natBits]
  · rw [if_neg h7]
    exact ⟨by simp only [bits, hs, List.append_assoc], ⟨show w.k + 1 < 8 by omega, hlt⟩⟩

theorem BitW.pushAll_spec : ∀ (e : List Bool) {w : BitW}, w.Inv →
    (w.pushAll e).bits = w.bits ++ e ∧ (w.pushAll e).Inv
  | [], _, hw => by simp [pushAll, hw]
  | b :: e, w, hw => by
    obtain ⟨h1, h2⟩ := w.push_spec hw b
    obtain ⟨h3, h4⟩ := pushAll_spec e h2
    exact ⟨by simp [pushAll, h3, h1], h4⟩

theorem toBytesAux_fromBytes : ∀ (L : List UInt8) (k c f : Nat), k < 8 → c < 2 ^ k →
    L.length + (if k = 0 then 0 else 1) ≤ f →
    toBytesAux f (fromBytes L ++ natBits k c) = L ++ (if k = 0 then [] else [c.toUInt8])
  | [], k, c, f, hk, hc, hf => by
    by_cases h0 : k = 0
    · subst h0; cases f <;> simp [fromBytes, natBits, toBytesAux]
    · obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [h0] at hf; omega⟩
      have hl := natBits_length k c
      have hne : natBits k c ≠ [] := by intro h; rw [h] at hl; simp at hl; omega
      simp only [fromBytes, List.nil_append, toBytesAux, hne, if_false, h0,
        List.take_of_length_le (show (natBits k c).length ≤ 8 by omega),
        List.drop_of_length_le (show (natBits k c).length ≤ 8 by omega), ofBits_natBits,
        Nat.mod_eq_of_lt hc]
      cases f <;> simp [toBytesAux]
  | b :: L, k, c, f, hk, hc, hf => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hl : (natBits 8 b.toNat).length = 8 := natBits_length 8 _
    have hne : natBits 8 b.toNat ++ (fromBytes L ++ natBits k c) ≠ [] := by
      intro h; have := congrArg List.length h; simp [hl] at this
    simp only [fromBytes, List.append_assoc, toBytesAux, hne, if_false,
      List.take_left' hl, List.drop_left' hl, ofBits_natBits]
    rw [toBytesAux_fromBytes L k c f hk hc (by simp at hf; omega)]
    simp

theorem BitW.finish_eq {w : BitW} (hw : w.Inv) : w.finish = toBytes w.bits := by
  have hl : w.bits.length = 8 * w.done.toList.length + w.k := by
    simp [bits, length_fromBytes, natBits_length]
  unfold toBytes
  rw [hl]
  unfold bits
  rw [toBytesAux_fromBytes _ _ _ _ hw.1 hw.2 (by split <;> omega), finish]
  split <;> simp

/-- `jamAux` with the table in a `Std.HashMap` and the bits written straight
into bytes; returns the writer, the table and the next bit position. The tail is
a tail call, so a list jams in constant stack. -/
def jamFastAux : Noun → FastTable → Nat → BitW → BitW × FastTable × Nat
  | n@(atom a), M, pos, w =>
    match M[n]? with
    | some p =>
      if bitLen a ≤ bitLen p then
        let e := false :: mat a; (w.pushAll e, M, pos + e.length)
      else
        let e := true :: true :: mat p; (w.pushAll e, M, pos + e.length)
    | none => let e := false :: mat a; (w.pushAll e, M.insert n pos, pos + e.length)
  | n@(cell h t), M, pos, w =>
    match M[n]? with
    | some p => let e := true :: true :: mat p; (w.pushAll e, M, pos + e.length)
    | none =>
      let rh := jamFastAux h (M.insert n pos) (pos + 2) ((w.push true).push false)
      jamFastAux t rh.2.1 rh.2.2 rh.1

/-- `jam` computed through `jamFastAux`. -/
def jamFast (n : Noun) : List UInt8 := (jamFastAux n ∅ 0 ⟨#[], 0, 0⟩).1.finish

/-- The hash table never lies: under a table that answers as the list table,
`jamFastAux` writes exactly `jamAux`'s bits, advances the position by their
length, and leaves a table that again answers as `jamAux`'s. -/
theorem jamFastAux_spec : ∀ (n : Noun) (M : FastTable) (m : JamTable) (pos : Nat) (w : BitW),
    w.Inv → (∀ a, M[a]? = lookupPos a m) →
    (jamFastAux n M pos w).1.bits = w.bits ++ (jamAux n m pos).1 ∧
    (jamFastAux n M pos w).1.Inv ∧
    (jamFastAux n M pos w).2.2 = pos + (jamAux n m pos).1.length ∧
    ∀ a, (jamFastAux n M pos w).2.1[a]? = lookupPos a (jamAux n m pos).2
  | atom x, M, m, pos, w, hw, hM => by
    simp only [jamFastAux, jamAux, hM (atom x)]
    split
    · split
      · exact ⟨(w.pushAll_spec _ hw).1, (w.pushAll_spec _ hw).2, rfl, hM⟩
      · exact ⟨(w.pushAll_spec _ hw).1, (w.pushAll_spec _ hw).2, rfl, hM⟩
    · exact ⟨(w.pushAll_spec _ hw).1, (w.pushAll_spec _ hw).2, rfl, fastTable_insert hM _ _⟩
  | cell h t, M, m, pos, w, hw, hM => by
    simp only [jamFastAux, jamAux, hM (cell h t)]
    split
    · exact ⟨(w.pushAll_spec _ hw).1, (w.pushAll_spec _ hw).2, rfl, hM⟩
    · obtain ⟨p1, i1⟩ := w.push_spec hw true
      obtain ⟨p2, i2⟩ := (w.push true).push_spec i1 false
      obtain ⟨h1, hi, h2, h3⟩ := jamFastAux_spec h _ _ (pos + 2) _ i2
        (fastTable_insert hM (cell h t) pos)
      rw [h2]
      obtain ⟨t1, ti, t2, t3⟩ := jamFastAux_spec t _ _ _ _ hi h3
      refine ⟨?_, ti, ?_, t3⟩
      · rw [t1, h1, p2, p1]; simp
      · rw [t2]; simp; omega

/-- Compiled code runs `jamFast` for `jam`. -/
@[csimp] theorem jam_eq_jamFast : @jam = @jamFast := by
  funext n
  have h0 : BitW.Inv ⟨#[], 0, 0⟩ := ⟨by decide, by decide⟩
  obtain ⟨h1, hi, -, -⟩ := jamFastAux_spec n ∅ [] 0 _ h0 (by intro a; simp [lookupPos])
  rw [jamFast, BitW.finish_eq hi, h1]
  rfl

/-- The byte string `jam` produces for the noun it cues to. -/
def canonical (bs : List UInt8) : Bool := (cue bs).map jam == some bs


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

/-! Pins for the mug / fast-codec layer. -/
/-- info: 'Minidregg.Theory.Noun.decEq_eq_decEqFast' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decEq_eq_decEqFast
/-- info: 'Minidregg.Theory.Noun.eq_iff_mugEq_and_structEq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms eq_iff_mugEq_and_structEq
/-- info: 'Minidregg.Theory.Noun.ne_of_mug_ne' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms ne_of_mug_ne
/-- info: 'Minidregg.Theory.Noun.bitLen_eq_bitLenFast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bitLen_eq_bitLenFast
/-- info: 'Minidregg.Theory.Noun.natBitsLoop_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms natBitsLoop_eq
/-- info: 'Minidregg.Theory.Noun.natBits_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms natBits_add
/-- info: 'Minidregg.Theory.Noun.natBits_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms natBits_mod
/-- info: 'Minidregg.Theory.Noun.natBits_eq_natBitsFast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms natBits_eq_natBitsFast
/-- info: 'Minidregg.Theory.Noun.getElem?_natBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms getElem?_natBits
/-- info: 'Minidregg.Theory.Noun.length_fromBytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms length_fromBytes
/-- info: 'Minidregg.Theory.Noun.getElem?_fromBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms getElem?_fromBytes
/-- info: 'Minidregg.Theory.Noun.getBit_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms getBit_eq
/-- info: 'Minidregg.Theory.Noun.countZerosF_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms countZerosF_eq
/-- info: 'Minidregg.Theory.Noun.readBits_eq_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readBits_eq_loop
/-- info: 'Minidregg.Theory.Noun.readValLoop_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readValLoop_add
/-- info: 'Minidregg.Theory.Noun.readVal_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readVal_eq
/-- info: 'Minidregg.Theory.Noun.rubF_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rubF_eq
/-- info: 'Minidregg.Theory.Noun.CueRel.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CueRel.insert
/-- info: 'Minidregg.Theory.Noun.decodeF_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodeF_rel
/-- info: 'Minidregg.Theory.Noun.cue_eq_cueFast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cue_eq_cueFast
/-- info: 'Minidregg.Theory.Noun.fastTable_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fastTable_insert
/-- info: 'Minidregg.Theory.Noun.natBits_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms natBits_snoc
/-- info: 'Minidregg.Theory.Noun.fromBytes_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms fromBytes_append
/-- info: 'Minidregg.Theory.Noun.BitW.push_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BitW.push_spec
/-- info: 'Minidregg.Theory.Noun.BitW.pushAll_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BitW.pushAll_spec
/-- info: 'Minidregg.Theory.Noun.toBytesAux_fromBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toBytesAux_fromBytes
/-- info: 'Minidregg.Theory.Noun.BitW.finish_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BitW.finish_eq
/-- info: 'Minidregg.Theory.Noun.jamFastAux_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms jamFastAux_spec
/-- info: 'Minidregg.Theory.Noun.jam_eq_jamFast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms jam_eq_jamFast

end Noun
end Minidregg.Theory
