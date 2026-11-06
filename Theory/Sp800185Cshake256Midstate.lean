/-
# Theory.Sp800185Cshake256Midstate -- cSHAKE256 over an absorbed prefix

A transcript that hashes many inputs sharing one long prefix (the Tower256 query seeds:
`queryPrefix ++ envelope (encodeLength a)` for every query `a`) re-absorbs that prefix once per
call. This module splits the sponge at the prefix:

* `absorbPadded_split` (specification): absorbing `padForRate (framed ++ suffix)` is absorbing
  the full rate blocks of `framed`, then the padded remainder `drop ++ suffix` from that state.
* `absorbFast` / `finishFast`: the split on the word path, with the absorbed prefix carried as
  bytes (`encode`: the 25 lanes little-endian, the padding delimiter, the unabsorbed tail;
  `decode_encode`).
* `cshake256AbsorbKernel` / `cshake256FinishKernel`: the kernel seams (`@[extern]`,
  `native/mini-kernels`), whose Lean bodies are those two functions, as
  `Sp800185Cshake256Native.cshake256Kernel`'s body is the fast path.
* **`cshake256_cached`**: for every customization, prefix and suffix, finishing the absorbed
  prefix with the suffix is `cshake256Bytes customization (prefix ++ suffix)`.

The trusted step is the same as for `mini_cshake256_32`: the Rust computes the Lean bodies,
pinned by Lean-authored vectors (`scripts/kernel-vectors.lean`, `cshake256_midstate` rows,
`cargo test -p mini-kernels --test conformance`). Every byte the kernels return is a function of
their arguments; no state lives outside the returned `ByteArray`.
-/
module

public import Theory.Sp800185Cshake256Native

@[expose] public section

namespace Minidregg.Compiler.Sp800185Cshake256

set_option autoImplicit false

/-! ## The split, on the specification -/

theorem absorbFrom_add (a b : Nat) (state : State) (bytes : List UInt8) :
    absorbFrom (a + b) state bytes =
      absorbFrom b (absorbFrom a state bytes) (bytes.drop (a * rateBytes)) := by
  induction a generalizing state bytes with
  | zero => simp [absorbFrom]
  | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 by omega]
      simp only [absorbFrom]
      rw [ih, List.drop_drop]
      congr 2
      simp only [rateBytes]
      omega

/-- Absorbing `k` blocks reads only the first `k` blocks. -/
theorem absorbFrom_append (k : Nat) (state : State) (head tail : List UInt8)
    (h : head.length = k * rateBytes) :
    absorbFrom k state (head ++ tail) = absorbFrom k state head := by
  induction k generalizing state head with
  | zero => simp [absorbFrom]
  | succ k ih =>
      have hle : rateBytes ≤ head.length := by rw [h, Nat.succ_mul]; omega
      simp only [absorbFrom]
      rw [List.take_append_of_le_length hle, List.drop_append_of_le_length hle]
      exact ih _ _ (by rw [List.length_drop, h, Nat.succ_mul]; omega)

/-- Padding reads only the length modulo the rate. -/
theorem padForRate_append (head tail : List UInt8) (suffix : UInt8)
    (h : head.length % rateBytes = 0) :
    padForRate (head ++ tail) suffix = head ++ padForRate tail suffix := by
  have hl : (head ++ tail).length % rateBytes = tail.length % rateBytes := by
    rw [List.length_append, Nat.add_mod, h, Nat.zero_add, Nat.mod_mod]
  unfold padForRate
  rw [hl]
  dsimp only
  by_cases hc : rateBytes - tail.length % rateBytes = 1
  · simp only [hc, ↓reduceIte, List.append_assoc]
  · simp only [hc, ↓reduceIte, List.append_assoc]

/-- **The sponge splits at the last full block of a prefix.** -/
theorem absorbPadded_split (framed suffix : List UInt8) (delim : UInt8) :
    absorbPadded (padForRate (framed ++ suffix) delim) =
      absorbFrom
        ((padForRate (framed.drop (framed.length / rateBytes * rateBytes) ++ suffix) delim).length /
          rateBytes)
        (absorbFrom (framed.length / rateBytes) zeroState framed)
        (padForRate (framed.drop (framed.length / rateBytes * rateBytes) ++ suffix) delim) := by
  generalize hk : framed.length / rateBytes = k
  have hkle : k * rateBytes ≤ framed.length := hk ▸ Nat.div_mul_le_self _ _
  generalize htail : padForRate (framed.drop (k * rateBytes) ++ suffix) delim = tail
  have hhead : (framed.take (k * rateBytes)).length = k * rateBytes := by
    rw [List.length_take]; omega
  have hpad : padForRate (framed ++ suffix) delim = framed.take (k * rateBytes) ++ tail := by
    rw [← htail, ← padForRate_append _ _ _ (by rw [hhead]; simp), ← List.append_assoc,
      List.take_append_drop]
  have hA : absorbFrom k zeroState framed =
      absorbFrom k zeroState (framed.take (k * rateBytes)) := by
    have h := absorbFrom_append k zeroState _ (framed.drop (k * rateBytes)) hhead
    rwa [List.take_append_drop] at h
  rw [hpad, hA]
  unfold absorbPadded
  rw [List.length_append, hhead,
    show (k * rateBytes + tail.length) / rateBytes = k + tail.length / rateBytes by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide : 0 < rateBytes), Nat.add_comm],
    absorbFrom_add, absorbFrom_append _ _ _ _ hhead, List.drop_left' hhead]

/-- The framed sponge input and its padding delimiter, as `cshake256Bytes` selects them. -/
def framedSpec (customization input : List UInt8) : List UInt8 :=
  if customization = [] then input else customizationPrefix customization ++ input

def delimiterSpec (customization : List UInt8) : UInt8 :=
  if customization = [] then 0x1f else 0x04

theorem cshake256Bytes_framed (customization input : List UInt8) :
    cshake256Bytes customization input =
      squeeze32 (absorbPadded (padForRate (framedSpec customization input)
        (delimiterSpec customization))) := rfl

theorem framedSpec_append (customization head tail : List UInt8) :
    framedSpec customization (head ++ tail) = framedSpec customization head ++ tail := by
  unfold framedSpec
  split <;> simp only [List.append_assoc]

namespace Midstate

open Fast Native

/-! ## The absorbed prefix as bytes -/

/-- `count` little-endian base-256 digits of `value`. -/
def digits : Nat → Nat → List UInt8
  | 0, _ => []
  | count + 1, value => UInt8.ofNat (value % 256) :: digits count (value / 256)

def undigits : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * undigits rest

theorem digits_length : ∀ (count value : Nat), (digits count value).length = count
  | 0, _ => rfl
  | count + 1, value => by rw [digits, List.length_cons, digits_length count (value / 256)]

theorem undigits_digits : ∀ (count value : Nat),
    undigits (digits count value) = value % 256 ^ count
  | 0, value => by simp [digits, undigits, Nat.mod_one]
  | count + 1, value => by
      rw [digits, undigits, undigits_digits count (value / 256), UInt8.toNat_ofNat', Nat.mod_mod,
        Nat.pow_succ', Nat.mod_mul]

/-- A lane's eight little-endian bytes, and the lane read back from the first eight bytes of a
list (missing bytes read as zero). -/
def laneBytes (x : UInt64) : List UInt8 := digits 8 x.toNat

def laneOf (bytes : List UInt8) : UInt64 := UInt64.ofNat (undigits (bytes.take 8))

theorem laneOf_laneBytes_append (x : UInt64) (rest : List UInt8) :
    laneOf (laneBytes x ++ rest) = x := by
  unfold laneOf laneBytes
  rw [List.take_left' (digits_length 8 _), undigits_digits,
    Nat.mod_eq_of_lt (by have := x.toNat_lt; simpa using this), UInt64.ofNat_toNat]

def lanes (s : KState) : List UInt64 :=
  [s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, s.a8, s.a9, s.a10, s.a11, s.a12, s.a13,
    s.a14, s.a15, s.a16, s.a17, s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24]

def ofLanes (l : List UInt64) : KState :=
  ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0, l.getD 5 0, l.getD 6 0,
    l.getD 7 0, l.getD 8 0, l.getD 9 0, l.getD 10 0, l.getD 11 0, l.getD 12 0, l.getD 13 0,
    l.getD 14 0, l.getD 15 0, l.getD 16 0, l.getD 17 0, l.getD 18 0, l.getD 19 0, l.getD 20 0,
    l.getD 21 0, l.getD 22 0, l.getD 23 0, l.getD 24 0⟩

theorem ofLanes_lanes (s : KState) : ofLanes (lanes s) = s := by
  cases s; rfl

def readLanes : Nat → List UInt8 → List UInt64
  | 0, _ => []
  | n + 1, bytes => laneOf bytes :: readLanes n (bytes.drop 8)

theorem readLanes_flatMap (xs : List UInt64) (rest : List UInt8) :
    readLanes xs.length (xs.flatMap laneBytes ++ rest) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.length_cons, readLanes, List.flatMap_cons, List.append_assoc,
        laneOf_laneBytes_append,
        List.drop_left' (show (laneBytes x).length = 8 from digits_length 8 _), ih]

/-- The absorbed prefix on the wire: 200 bytes of lanes, the delimiter, the unabsorbed tail. -/
def encode (s : KState) (delim : UInt8) (pending : List UInt8) : List UInt8 :=
  (lanes s).flatMap laneBytes ++ delim :: pending

/-- Total: a short list reads as zero-filled. -/
def decode (bytes : List UInt8) : KState × UInt8 × List UInt8 :=
  (ofLanes (readLanes 25 bytes), (bytes.drop 200).headD 0, (bytes.drop 200).drop 1)

theorem lanesBytes_length (s : KState) : ((lanes s).flatMap laneBytes).length = 200 := by
  simp [lanes, laneBytes, digits_length]

theorem decode_encode (s : KState) (delim : UInt8) (pending : List UInt8) :
    decode (encode s delim pending) = (s, delim, pending) := by
  have h := readLanes_flatMap (lanes s) (delim :: pending)
  rw [show (lanes s).length = 25 from rfl] at h
  unfold decode encode
  rw [h, ofLanes_lanes, List.drop_left' (lanesBytes_length s)]
  rfl

/-! ## The two halves on the word path -/

def framedBA (customization input : ByteArray) : ByteArray :=
  if customization.data.toList = [] then input
  else pushList (pushList ByteArray.empty (customizationPrefix customization.data.toList))
    input.data.toList

def delimiterOf (customization : ByteArray) : UInt8 :=
  if customization.data.toList = [] then 0x1f else 0x04

theorem framedBA_data (customization input : List UInt8) :
    (framedBA (bytesOfList customization) (bytesOfList input)).data.toList =
      framedSpec customization input := by
  unfold framedBA framedSpec
  rw [bytesOfList_toList]
  split
  · exact bytesOfList_toList input
  · rw [pushList_data, pushList_data, empty_data, List.nil_append, bytesOfList_toList]

theorem delimiterOf_bytes (customization : List UInt8) :
    delimiterOf (bytesOfList customization) = delimiterSpec customization := by
  unfold delimiterOf delimiterSpec
  rw [bytesOfList_toList]

/-- Absorb the full rate blocks of the framed prefix; carry the rest. -/
def absorbFast (customization pre : ByteArray) : ByteArray :=
  let framed := framedBA customization pre
  let full := framed.size / rateBytes
  bytesOfList (encode (absorbLoop framed full 0 zeroS) (delimiterOf customization)
    (framed.data.toList.drop (full * rateBytes)))

/-- Append the suffix to the carried tail, pad, absorb, squeeze. -/
def finishFast (midstate suffix : ByteArray) : ByteArray :=
  let parts := decode midstate.data.toList
  let tail := padBA (pushList (bytesOfList parts.2.2) suffix.data.toList) parts.2.1
  bytesOfList (squeezeS (absorbLoop tail (tail.size / rateBytes) 0 parts.1))

/-- **The absorb seam.** The Lean body is `absorbFast`; the compiled code is
`mini_cshake256_absorb` (`native/mini-kernels`, `cshake256_absorb`). Both arguments borrowed. -/
@[extern "mini_cshake256_absorb"]
def cshake256AbsorbKernel (customization pre : @& ByteArray) : ByteArray :=
  absorbFast customization pre

/-- **The finish seam.** The Lean body is `finishFast`; the compiled code is
`mini_cshake256_finish_32` (`cshake256_finish_32`). Both arguments borrowed. -/
@[extern "mini_cshake256_finish_32"]
def cshake256FinishKernel (midstate suffix : @& ByteArray) : ByteArray :=
  finishFast midstate suffix

/-- **Finishing an absorbed prefix is hashing the whole input**, for every customization,
prefix and suffix. -/
theorem cshake256_cached (customization pre suffix : List UInt8) :
    (cshake256FinishKernel (cshake256AbsorbKernel (bytesOfList customization) (bytesOfList pre))
        (bytesOfList suffix)).data.toList =
      cshake256Bytes customization (pre ++ suffix) := by
  unfold cshake256FinishKernel cshake256AbsorbKernel finishFast absorbFast
  simp only [bytesOfList_toList, decode_encode]
  rw [squeeze_fast_eq, absorb_fast_eq, absorb_fast_eq, size_eq_length, size_eq_length,
    padBA_data, pushList_data, bytesOfList_toList, framedBA_data, delimiterOf_bytes,
    zeroS_toState, List.drop_zero, List.drop_zero, cshake256Bytes_framed, framedSpec_append,
    absorbPadded_split]

end Midstate

end Minidregg.Compiler.Sp800185Cshake256

/-- info: 'Minidregg.Compiler.Sp800185Cshake256.absorbPadded_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.Sp800185Cshake256.absorbPadded_split
/-- info: 'Minidregg.Compiler.Sp800185Cshake256.Midstate.cshake256_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.Sp800185Cshake256.Midstate.cshake256_cached
