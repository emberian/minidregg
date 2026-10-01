/-
# Kernel.DomainEpoch — the epoch record a channel domain commits to the Store (CHANNELS.md §2.4, §9 row 8)

A channel domain's relay (its sequencer) appends ONE `EpochRecord` per epoch to the domain's
channel cell, a K-STREAM `stream` cell born `--in R` under the sequencer's author law. A cell of
the channel is not a kernel turn; the kernel sees one record per domain per epoch.

* **The record** (`EpochRecord`): `domain | epoch | class | n | E tick roots | absentCommit`, a
  fixed-width big-endian codec whose decoder accepts exactly the encodings
  (`epochRecord_decode_canonical`, `epochRecord_encode_injective`, `epochRecord_size`). It rides as
  the append's payload; the append's topic is `channelTopic domain epoch`, which the cell stores.
* **The absent opening** (`AbsentOpening {mask, salt}`): one byte per position (`E · n` of them,
  checked against the record's class and `n` when the opening is decoded, `.maskLength` by name)
  and a 32-byte salt. `commitAbsent` is K-HASHEQ's construction — cSHAKE256 of `value ‖ blinder`
  under a per-purpose customization — at `DREGG.CHANNEL.ABSENT/v1`. The opening goes to the operator
  and the witnesses; it is never in the channel cell.
* **The law** (`ChannelLaw`, decided by `checkRecord`): the class is known and the record carries
  exactly its `E` roots and `0 < n ≤ 2¹⁶`; and after a previous record, the domain is the same, the
  epoch is exactly one more, and the author is the previous record's author (the sequencer). The
  kernel runs it at the append (`admitAppend`, where the payload bytes are) and the registry checks
  its store-level shadow (`ChannelStoreLaw`, over the topics and authors the cell holds) on every
  loaded and final stream cell.
* **What the record proves, and to whom**: `committed_cells_agree` (any two holders of the record),
  `own_omission_evident` (a member about its own slot, no opening needed), `omission_evident` (the
  holders of an opening: the operator and the witnesses), `relay_equivocation_transferable` (anyone
  with the sequencer's key), and the limit `silent_and_dropped_indistinguishable`.

Binding is never assumed: every binding statement is "equal, or a collision of the named
cSHAKE256 instance" — `Pred.HashEqDigest.Collision`, the carrier K-HASHEQ's `binds_or_collides`
already names. Hiding of `absentCommit` is K-HASHEQ's `HashEqHiding` shape (assumed, not proved, used
by no theorem here).

**Two modules, one namespace.** This one is what a relay, a member and a witness run: the codecs, the
commitment, the seal, the opening, the tick roots and the omission theorems. It imports `Init`, the
executable cSHAKE256 core, `Pred.HashEqDigest` and `Theory.Channel` only, so the channel library a
member's phone loads carries no Mathlib. The kernel's side — `Prev`, `ChannelLaw`/`checkRecord` (an
author is a `SubjectId`), `admitAppend`, `ChannelStoreLaw` and the in-Store chain — is
`Kernel.DomainEpochLaw`, under the same names. The `#assert_axioms` pins of both live in
`Kernel.DomainEpochAudit`.
-/
import Compiler.Sp800185Cshake256Core
import Pred.HashEqDigest
import Theory.Channel

namespace Minidregg.Kernel.DomainEpoch

open Minidregg.Theory.Channel (Blob fit Profile U16 be16 rd16 rd16_be16 Header Cell Schedule FillPrf
  fillCell Submission Source profileOfId cell_encode_injective)
open Minidregg.Pred.HashEqDigest (be ofBE Collision utf8 length_be)
open Minidregg.Compiler.Sp800185Cshake256 (cshake256Bytes cshake256Bytes_length)

set_option autoImplicit false

/-! ## §1. Hashes: the kernel's one cSHAKE256, one customization per purpose -/

/-- A 32-byte digest. -/
abbrev Digest := Blob 32

/-- cSHAKE256 under `tag`, as a 32-byte digest. -/
def hashWith (tag : List UInt8) (bytes : List UInt8) : Digest :=
  ⟨cshake256Bytes tag bytes, cshake256Bytes_length _ _⟩

/-- The absent-mask commitment (K-HASHEQ's commit, this purpose's customization). -/
def absentTag : List UInt8 := utf8 "DREGG.CHANNEL.ABSENT/v1"
/-- A committed cell's digest. -/
def cellTag : List UInt8 := utf8 "DREGG.CHANNEL.CELL/v1"
/-- A tick vector's root over its cells' digests in slot order. -/
def tickTag : List UInt8 := utf8 "DREGG.CHANNEL.TICK/v1"
/-- What the sequencer signs, outside the kernel, when it hands a record to a witness. -/
def sigTag : List UInt8 := utf8 "DREGG.CHANNEL.EPOCH-SIG/v1"

/-- Equal digests of different inputs are a collision of that cSHAKE256 instance. -/
theorem collision_of {tag a b : List UInt8} (ne : a ≠ b) (eq : hashWith tag a = hashWith tag b) :
    Collision (cshake256Bytes tag) :=
  ⟨a, b, ne, congrArg ofBE (congrArg Blob.val eq)⟩

/-! ## §2. Fixed-width bytes -/

theorem ofBE_append (xs : List UInt8) (b : UInt8) : ofBE (xs ++ [b]) = ofBE xs * 256 + b.toNat := by
  simp [ofBE, List.foldl_append]

theorem ofBE_be (w n : Nat) (h : n < 256 ^ w) : ofBE (be w n) = n := by
  induction w generalizing n with
  | zero => simp at h; subst h; rfl
  | succ w ih =>
    have hpow : 256 ^ (w + 1) = 256 ^ w * 256 := Nat.pow_succ ..
    have hq : n / 256 < 256 ^ w := (Nat.div_lt_iff_lt_mul (by decide)).mpr (hpow ▸ h)
    simp only [be]
    rw [ofBE_append, ih _ hq, UInt8.toNat_ofNat']
    have h8 : (2 : Nat) ^ 8 = 256 := by decide
    rw [h8]
    omega

/-- Concatenated fixed-width blobs determine the list. -/
theorem flat_injective : ∀ {xs ys : List Digest}, xs.flatMap Blob.val = ys.flatMap Blob.val → xs = ys
  | [], [], _ => rfl
  | [], y :: ys, h => by
      have := congrArg List.length h
      simp [y.property] at this; omega
  | x :: xs, [], h => by
      have := congrArg List.length h
      simp [x.property] at this
  | x :: xs, y :: ys, h => by
      simp only [List.flatMap_cons] at h
      obtain ⟨hx, hr⟩ := List.append_inj h (by rw [x.property, y.property])
      rw [Blob.ext hx, flat_injective hr]

theorem flat_length {k : Nat} : ∀ xs : List (Blob k), (xs.flatMap Blob.val).length = k * xs.length
  | [] => by simp
  | x :: xs => by
      simp only [List.flatMap_cons, List.length_append, x.property, flat_length xs, List.length_cons,
        Nat.mul_add, Nat.mul_one]
      omega

/-- `k` 32-byte chunks of a byte string (structural, so it reduces in the kernel). -/
def chunks : Nat → List UInt8 → List Digest
  | 0, _ => []
  | k + 1, bytes => fit 32 bytes :: chunks k (bytes.drop 32)

theorem chunks_flat : ∀ (xs : List Digest) (rest : List UInt8),
    chunks xs.length (xs.flatMap Blob.val ++ rest) = xs
  | [], _ => rfl
  | x :: xs, rest => by
      have hx := x.property
      simp only [chunks, List.flatMap_cons, List.append_assoc]
      rw [List.drop_left' hx, chunks_flat xs rest]
      congr 1
      apply Blob.ext
      rw [Minidregg.Theory.Channel.fit_val_of_le _ (by simp [hx])]
      exact List.take_left' hx

/-! ## §3. The epoch record -/

/-- **`EpochRecord`.** One per domain per epoch, appended by the sequencer to the domain's channel
cell. `classId` names the class (`Theory.Channel.profileOfId`: 0 P0 · 1 P1 · 2 P1 phone · 3 P2), so
`E` is the class's; `n` is the schedule's slot count at the epoch; `tickRoots[t]` is the root of tick
`t`'s vector (`vectorRoot`); `absentCommit` hides the absent mask. The signer is not a field: the
record is the payload of an append, whose signing subject is the stream record's `author`. -/
structure EpochRecord where
  domain : U16
  epoch : UInt64
  classId : UInt8
  n : UInt32
  tickRoots : List Digest
  absentCommit : Digest
  deriving DecidableEq

/-- `domain 2 | epoch 8 | class 1 | n 4 | tickRoots 32·k | absentCommit 32`, big-endian. The root
count is the length's: there is no count field to disagree with it. -/
def EpochRecord.encode (r : EpochRecord) : List UInt8 :=
  be16 r.domain ++ be 8 r.epoch.toNat ++ [r.classId] ++ be 4 r.n.toNat ++
    r.tickRoots.flatMap Blob.val ++ r.absentCommit.val

/-- The total parse: every field is a slice of the input. -/
def EpochRecord.parse (bytes : List UInt8) : EpochRecord :=
  let body := bytes.drop 15
  let k := (body.length - 32) / 32
  { domain := rd16 (bytes.getD 0 0) (bytes.getD 1 0)
    epoch := UInt64.ofNat (ofBE ((bytes.drop 2).take 8))
    classId := bytes.getD 10 0
    n := UInt32.ofNat (ofBE ((bytes.drop 11).take 4))
    tickRoots := chunks k body
    absentCommit := fit 32 (body.drop (32 * k)) }

/-- **The decoder accepts exactly the encodings**: parse, then re-encode and compare. -/
def EpochRecord.decode (bytes : List UInt8) : Option EpochRecord :=
  let r := EpochRecord.parse bytes
  if r.encode = bytes then some r else none

theorem epochRecord_size (r : EpochRecord) : r.encode.length = 47 + 32 * r.tickRoots.length := by
  simp only [EpochRecord.encode, List.length_append, length_be, flat_length, r.absentCommit.property,
    List.length_cons, List.length_nil]
  simp [be16]
  omega

theorem epochRecord_parse_encode (r : EpochRecord) : EpochRecord.parse r.encode = r := by
  obtain ⟨d, e, c, n, roots, commit⟩ := r
  have he : e.toNat < 256 ^ 8 := Nat.lt_of_lt_of_eq e.toNat_lt (by decide)
  have hn : n.toNat < 256 ^ 4 := Nat.lt_of_lt_of_eq n.toNat_lt (by decide)
  have hc := commit.property
  have hfl := flat_length roots
  have hb8 := length_be 8 e.toNat
  have hb4 := length_be 4 n.toNat
  -- the encoding, in the shape the parse reads it
  have shape : (EpochRecord.encode ⟨d, e, c, n, roots, commit⟩) =
      (d.val / 256).toUInt8 :: (d.val % 256).toUInt8 ::
        (be 8 e.toNat ++ c :: (be 4 n.toNat ++ (roots.flatMap Blob.val ++ commit.val))) := by
    simp [EpochRecord.encode, be16]
  have d2 : (be 8 e.toNat ++ c :: (be 4 n.toNat ++ (roots.flatMap Blob.val ++ commit.val))).drop 9 =
      be 4 n.toNat ++ (roots.flatMap Blob.val ++ commit.val) := by
    rw [show 9 = (be 8 e.toNat).length + 1 by rw [hb8], List.drop_append]
    rfl
  have d13 : (be 4 n.toNat ++ (roots.flatMap Blob.val ++ commit.val)).drop 4 =
      roots.flatMap Blob.val ++ commit.val := List.drop_left' hb4
  have hk : ((roots.flatMap Blob.val ++ commit.val).length - 32) / 32 = roots.length := by
    simp only [List.length_append, hfl, hc]; omega
  have hcls : (be 8 e.toNat ++ c :: (be 4 n.toNat ++ (roots.flatMap Blob.val ++ commit.val)))[8]? =
      some c := by
    rw [List.getElem?_append_right (by simp [hb8])]; simp [hb8]
  simp only [EpochRecord.parse, shape]
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons, List.drop_zero]
  rw [rd16_be16]
  have e2 : List.take 8 (be 8 e.toNat ++ c :: (be 4 n.toNat ++ (roots.flatMap Blob.val ++ commit.val))) =
      be 8 e.toNat := List.take_left' hb8
  rw [e2, ofBE_be _ _ he, UInt64.ofNat_toNat]
  have g10 : (be 8 e.toNat ++ c :: (be 4 n.toNat ++ (roots.flatMap Blob.val ++ commit.val))).getD 8 0 = c := by
    rw [List.getD_eq_getElem?_getD, hcls]; rfl
  rw [g10]
  rw [show (be 8 e.toNat ++ c :: (be 4 n.toNat ++ (roots.flatMap Blob.val ++ commit.val))).drop 9 =
      be 4 n.toNat ++ (roots.flatMap Blob.val ++ commit.val) from d2]
  rw [List.take_left' hb4, ofBE_be _ _ hn, UInt32.ofNat_toNat]
  have d13full : (be 8 e.toNat ++ c :: (be 4 n.toNat ++ (roots.flatMap Blob.val ++ commit.val))).drop 13 =
      roots.flatMap Blob.val ++ commit.val := by
    have : (be 8 e.toNat ++ c :: (be 4 n.toNat ++ (roots.flatMap Blob.val ++ commit.val))).drop 13 =
        ((be 8 e.toNat ++ c :: (be 4 n.toNat ++ (roots.flatMap Blob.val ++ commit.val))).drop 9).drop 4 := by
      simp [List.drop_drop]
    rw [this, d2, d13]
  rw [d13full, hk, chunks_flat, List.drop_left' (by rw [hfl])]
  rw [show fit 32 commit.val = commit from Blob.ext (Minidregg.Theory.Channel.fit_val_of_length _ hc)]

/-- The accepting pole: every encoding decodes to its record. -/
theorem epochRecord_decode_encode (r : EpochRecord) : EpochRecord.decode r.encode = some r := by
  simp [EpochRecord.decode, epochRecord_parse_encode]

/-- **`epochRecord_decode_canonical`.** An accepted byte string is the record's unique encoding. -/
theorem epochRecord_decode_canonical {bytes : List UInt8} {r : EpochRecord}
    (accepted : EpochRecord.decode bytes = some r) : r.encode = bytes := by
  dsimp only [EpochRecord.decode] at accepted
  split at accepted
  · rename_i h; cases accepted; exact h
  · cases accepted

theorem epochRecord_decode_eq_some_iff (bytes : List UInt8) (r : EpochRecord) :
    EpochRecord.decode bytes = some r ↔ r.encode = bytes :=
  ⟨epochRecord_decode_canonical, fun h => h ▸ epochRecord_decode_encode r⟩

theorem epochRecord_encode_injective : Function.Injective EpochRecord.encode := by
  intro a b h
  rw [← epochRecord_parse_encode a, h, epochRecord_parse_encode]

/-- The refusing pole: a byte string of a length no record has is refused. -/
theorem epochRecord_decode_refuses_length {bytes : List UInt8}
    (h : bytes.length < 47 ∨ (bytes.length - 47) % 32 ≠ 0) : EpochRecord.decode bytes = none := by
  cases hd : EpochRecord.decode bytes with
  | none => rfl
  | some r =>
    have := congrArg List.length (epochRecord_decode_canonical hd)
    rw [epochRecord_size] at this
    omega

/-! ## §4. The absent opening and its commitment -/

/-- **`AbsentOpening`.** `mask[t · n + ρ] = true` iff the relay marked position `(t, ρ)` absent and put
a fill cell there; `salt` is the 32-byte blinder (§2.4: `KMAC(relaySecret, domain ‖ epoch ‖ "absent")`,
computed outside Lean). Sealed to the witness set with the head and held by the operator; never in the
channel cell. -/
structure AbsentOpening where
  mask : List Bool
  salt : Digest
  deriving DecidableEq

def bit (b : Bool) : UInt8 := if b then 1 else 0

/-- One byte per position (`0`/`1`), then the salt. Its length is `E · n + 32`; the decoder takes
`E` and `n` from the record it opens. -/
def AbsentOpening.encode (o : AbsentOpening) : List UInt8 := o.mask.map bit ++ o.salt.val

/-- Why an opening refuses. -/
inductive OpeningRefusal where
  /-- the opening does not hold exactly `E · n` mask bytes (and a salt) -/
  | maskLength
  /-- a mask byte other than `0` or `1` -/
  | maskByte
  /-- the record's class is unknown, so `E` is unknown -/
  | unknownClass
  /-- the opening does not open the record's `absentCommit` -/
  | notOpening
  deriving DecidableEq, Repr

/-- Decode an opening of an epoch of `E` ticks and `n` slots. The length check is ON THE OPENING. -/
def AbsentOpening.decode (E n : Nat) (bytes : List UInt8) : Except OpeningRefusal AbsentOpening :=
  if bytes.length ≠ E * n + 32 then .error .maskLength
  else if (bytes.take (E * n)).all (· ≤ 1) then
    .ok ⟨(bytes.take (E * n)).map (· == 1), fit 32 (bytes.drop (E * n))⟩
  else .error .maskByte

theorem bit_injective : Function.Injective bit := by
  intro a b h; cases a <;> cases b <;> first | rfl | (simp [bit] at h)

/-- The mask bytes determine the mask. -/
theorem map_bit_injective : ∀ {l₁ l₂ : List Bool}, l₁.map bit = l₂.map bit → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [bit_injective h.1, map_bit_injective h.2]

theorem absentOpening_encode_injective : Function.Injective AbsentOpening.encode := by
  intro a b h
  have hl := congrArg List.length h
  simp only [AbsentOpening.encode, List.length_append, List.length_map, a.salt.property,
    b.salt.property] at hl
  obtain ⟨hm, hs⟩ := List.append_inj h (by simp; omega)
  cases a; cases b
  simp only [AbsentOpening.mk.injEq]
  exact ⟨map_bit_injective hm, Blob.ext hs⟩

theorem absentOpening_size (o : AbsentOpening) : o.encode.length = o.mask.length + 32 := by
  simp [AbsentOpening.encode, o.salt.property]

/-- The accepting pole: an opening of `E · n` positions decodes to itself. -/
theorem absentOpening_decode_encode (E n : Nat) (o : AbsentOpening) (len : o.mask.length = E * n) :
    AbsentOpening.decode E n o.encode = .ok o := by
  obtain ⟨mask, salt⟩ := o
  have hs := salt.property
  simp only at len
  simp only [AbsentOpening.decode, AbsentOpening.encode, List.length_append, List.length_map, len, hs,
    ne_eq, not_true_eq_false, if_false]
  have ht : (mask.map bit ++ salt.val).take (E * n) = mask.map bit := List.take_left' (by simp [len])
  have hd : (mask.map bit ++ salt.val).drop (E * n) = salt.val := List.drop_left' (by simp [len])
  rw [ht, hd]
  have hall : (mask.map bit).all (· ≤ 1) = true := by
    simp only [List.all_map, List.all_eq_true, Function.comp]
    intro b _; cases b <;> decide
  rw [if_pos hall]
  congr 2
  · rw [List.map_map]; conv => rhs; rw [← List.map_id mask]
    apply List.map_congr_left; intro b _; cases b <;> rfl
  · exact Blob.ext (Minidregg.Theory.Channel.fit_val_of_length _ hs)

/-- **The canonical pole**: an accepted opening is the byte string's unique reading. -/
theorem absentOpening_decode_canonical {E n : Nat} {bytes : List UInt8} {o : AbsentOpening}
    (accepted : AbsentOpening.decode E n bytes = .ok o) : o.encode = bytes ∧ o.mask.length = E * n := by
  unfold AbsentOpening.decode at accepted
  split at accepted
  · cases accepted
  · rename_i hlen
    split at accepted
    · rename_i hall
      cases accepted
      have hle : E * n ≤ bytes.length := by omega
      refine ⟨?_, by simp [hle]⟩
      simp only [AbsentOpening.encode, List.map_map]
      have hdl : (bytes.drop (E * n)).length = 32 := by simp; omega
      rw [Minidregg.Theory.Channel.fit_val_of_length _ hdl]
      conv => rhs; rw [← List.take_append_drop (E * n) bytes]
      congr 1
      conv => rhs; rw [← List.map_id (bytes.take (E * n))]
      apply List.map_congr_left
      intro x hx
      have := List.all_eq_true.mp hall x hx
      simp only [decide_eq_true_eq] at this
      simp only [Function.comp, bit, id]
      by_cases h1 : x = 1
      · simp [h1]
      · have h0 : x = 0 := by
          have := UInt8.le_iff_toNat_le.mp this
          apply UInt8.toNat_inj.mp; have : x.toNat ≠ 1 := fun h => h1 (UInt8.toNat_inj.mp h)
          simp at *; omega
        simp [h0]
    · cases accepted

/-- **`maskLength`, by name**: an opening of the wrong length refuses whatever its bytes. -/
theorem absentOpening_wrong_length_refused {E n : Nat} {bytes : List UInt8}
    (wrong : bytes.length ≠ E * n + 32) : AbsentOpening.decode E n bytes = .error .maskLength := by
  simp [AbsentOpening.decode, wrong]

/-- The commitment, under any byte hash (the refutable pole instantiates a weak one). -/
def commitAbsentWith (H : Minidregg.Pred.HashEqDigest.Hash) (o : AbsentOpening) : List UInt8 := H o.encode

/-- **`commitAbsent`**: cSHAKE256 under `DREGG.CHANNEL.ABSENT/v1` of `mask ‖ salt` (K-HASHEQ's
`H(value ‖ blinder)`, this purpose's customization). -/
def commitAbsent (o : AbsentOpening) : Digest := hashWith absentTag o.encode

theorem commitAbsent_val (o : AbsentOpening) :
    (commitAbsent o).val = commitAbsentWith (cshake256Bytes absentTag) o := rfl

/-- **Binds or collides**, for any hash. -/
theorem opening_binds_with (H : Minidregg.Pred.HashEqDigest.Hash) {o₁ o₂ : AbsentOpening}
    (same : commitAbsentWith H o₁ = commitAbsentWith H o₂) : o₁ = o₂ ∨ Collision H := by
  by_cases h : o₁ = o₂
  · exact .inl h
  · exact .inr ⟨o₁.encode, o₂.encode, fun he => h (absentOpening_encode_injective he),
      congrArg ofBE same⟩

/-- **`opening_binds`.** Two openings of one `absentCommit` are the same opening (in particular they
agree on the mask), or the deployed cSHAKE256 instance has a collision — `Collision` is the carrier
K-HASHEQ's `binds_or_collides` names; no axiom is added. -/
theorem opening_binds {o₁ o₂ : AbsentOpening} (same : commitAbsent o₁ = commitAbsent o₂) :
    o₁.mask = o₂.mask ∨ Collision (cshake256Bytes absentTag) :=
  have h : commitAbsentWith (cshake256Bytes absentTag) o₁ = commitAbsentWith (cshake256Bytes absentTag) o₂ :=
    congrArg Blob.val same
  (opening_binds_with _ h).imp (congrArg AbsentOpening.mask) id

/-- The refutable pole: under the length hash binding fails — two different masks of one length
commit identically. So `opening_binds` is carried by the hash, not by the encoding. -/
theorem lengthHash_opening_binding_fails :
    commitAbsentWith Minidregg.Pred.HashEqDigest.lengthHash ⟨[true, false], ⟨List.replicate 32 0, rfl⟩⟩ =
      commitAbsentWith Minidregg.Pred.HashEqDigest.lengthHash ⟨[false, true], ⟨List.replicate 32 0, rfl⟩⟩ ∧
    ([true, false] : List Bool) ≠ [false, true] := by
  decide

/-! ## §5. The channel law -/

/-- Why the channel law refuses an append. Each is a refusal by name. -/
inductive Refusal where
  /-- the topic starts with the channel magic but is not a channel topic -/
  | malformedTopic
  /-- a channel record into an ordinary stream, or an ordinary entry into a channel stream -/
  | kindMismatch
  /-- the payload is not the canonical encoding of an `EpochRecord` -/
  | malformedRecord
  /-- the topic's (domain, epoch) is not the record's -/
  | topicMismatch
  /-- the record names no published class -/
  | unknownClass
  /-- the record does not carry exactly its class's `E` tick roots -/
  | rootCount
  /-- `n = 0` or `n > 2¹⁶` -/
  | slotCount
  /-- another domain's record in this domain's stream -/
  | foreignDomain
  /-- a gap: the epoch is more than one past the previous record's -/
  | epochGap
  /-- a repeat or out of order: the epoch is not after the previous record's -/
  | epochNotAfter
  /-- the record's author is not the stream's sequencer (the previous record's author) -/
  | foreignAuthor
  deriving DecidableEq, Repr

/-- The record's own shape: a published class, exactly its `E` roots, `0 < n ≤ 2¹⁶`. -/
def EpochRecord.WellFormed (r : EpochRecord) : Prop :=
  ∃ P, profileOfId r.classId = some P ∧ r.tickRoots.length = P.E ∧ 0 < r.n.toNat ∧ r.n.toNat ≤ 65536


/-! ## §6. The channel topic and the kernel's admission of an append -/

/-- The channel topic's magic, 22 bytes. -/
def topicMagic : List UInt8 := utf8 "DREGG.CHANNEL.EPOCH/v1"

theorem topicMagic_length : topicMagic.length = 22 := by decide

/-- The topic of a channel record's append, 32 bytes: magic, domain, epoch. The stream cell stores
it, so the registry's store law reads the chain from it. -/
def channelTopic (d : U16) (e : UInt64) : List UInt8 := topicMagic ++ be16 d ++ be 8 e.toNat

inductive TopicClass where
  | ordinary
  | channel (d : U16) (e : UInt64)
  | malformed
  deriving DecidableEq, Repr

/-- Read a topic: not starting with the magic is an ordinary stream topic. -/
def classifyTopic (topic : List UInt8) : TopicClass :=
  if topic.take 22 = topicMagic then
    let d := rd16 (topic.getD 22 0) (topic.getD 23 0)
    let e := UInt64.ofNat (ofBE ((topic.drop 24).take 8))
    if topic = channelTopic d e then .channel d e else .malformed
  else .ordinary

theorem classifyTopic_channelTopic (d : U16) (e : UInt64) :
    classifyTopic (channelTopic d e) = .channel d e := by
  have hm := topicMagic_length
  have hb8 := length_be 8 e.toNat
  have he : e.toNat < 256 ^ 8 := Nat.lt_of_lt_of_eq e.toNat_lt (by decide)
  have hshape : channelTopic d e = topicMagic ++ ((d.val / 256).toUInt8 :: (d.val % 256).toUInt8 :: be 8 e.toNat) := by
    simp [channelTopic, be16]
  have h22 : (channelTopic d e).take 22 = topicMagic := by rw [hshape, List.take_left' hm]
  have hd : (channelTopic d e).drop 22 = (d.val / 256).toUInt8 :: (d.val % 256).toUInt8 :: be 8 e.toNat := by
    rw [hshape, List.drop_left' hm]
  have g22 : (channelTopic d e).getD 22 0 = (d.val / 256).toUInt8 := by
    rw [List.getD_eq_getElem?_getD, show (22 : Nat) = 22 + 0 from rfl, ← List.getElem?_drop, hd]; rfl
  have g23 : (channelTopic d e).getD 23 0 = (d.val % 256).toUInt8 := by
    rw [List.getD_eq_getElem?_getD, show (23 : Nat) = 22 + 1 from rfl, ← List.getElem?_drop, hd]; rfl
  have d24 : ((channelTopic d e).drop 24).take 8 = be 8 e.toNat := by
    have : (channelTopic d e).drop 24 = ((channelTopic d e).drop 22).drop 2 := by simp [List.drop_drop]
    rw [this, hd]; simp only [List.drop_succ_cons, List.drop_zero]
    exact List.take_of_length_le (Nat.le_of_eq hb8)
  unfold classifyTopic
  rw [if_pos h22]
  simp only [g22, g23, d24, rd16_be16, ofBE_be _ _ he, UInt64.ofNat_toNat, if_true]

theorem channelTopic_length (d : U16) (e : UInt64) : (channelTopic d e).length = 32 := by
  simp [channelTopic, be16, topicMagic_length]

/-! ## §8. What a record commits: cells, tick roots, and what each holder can check -/

section Commit
variable {P : Profile}

/-- A committed cell's digest. -/
def cellDigest (c : Cell P) : Digest := hashWith cellTag c.encode

/-- A tick root over the cells' digests in slot order. (A flat hash, not a Merkle tree: at T3 every
member downloads the whole vector. Lanes that need paths swap this one definition.) -/
def tickRoot (ds : List Digest) : Digest := hashWith tickTag (ds.flatMap Blob.val)

def vectorRoot (v : List (Cell P)) : Digest := tickRoot (v.map cellDigest)

theorem cell_binds {a b : Cell P} (same : cellDigest a = cellDigest b) :
    a = b ∨ Collision (cshake256Bytes cellTag) := by
  by_cases h : a = b
  · exact .inl h
  · exact .inr (collision_of (fun he => h (cell_encode_injective he)) same)

theorem tick_binds {ds₁ ds₂ : List Digest} (same : tickRoot ds₁ = tickRoot ds₂) :
    ds₁ = ds₂ ∨ Collision (cshake256Bytes tickTag) := by
  by_cases h : ds₁ = ds₂
  · exact .inl h
  · exact .inr (collision_of (fun he => h (flat_injective he)) same)

theorem digests_bind : ∀ {v₁ v₂ : List (Cell P)}, v₁.map cellDigest = v₂.map cellDigest →
    v₁ = v₂ ∨ Collision (cshake256Bytes cellTag)
  | [], [], _ => .inl rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: v₁, b :: v₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases cell_binds h.1 with hab | col
    · rcases digests_bind h.2 with hv | col
      · exact .inl (by rw [hab, hv])
      · exact .inr col
    · exact .inr col

/-- A member holds `v` as tick `t` of record `r`: the vector opens the committed root. -/
def Opens (r : EpochRecord) (t : Nat) (v : List (Cell P)) : Prop := r.tickRoots[t]? = some (vectorRoot v)

/-- **`committed_cells_agree`.** Two members holding the same record, each with a vector per tick that
opens its roots, agree on every committed cell's digest at every tick — or the tick hash collides. -/
theorem committed_cells_agree (r : EpochRecord) (v₁ v₂ : Nat → List (Cell P))
    (h₁ : ∀ t < r.tickRoots.length, Opens r t (v₁ t)) (h₂ : ∀ t < r.tickRoots.length, Opens r t (v₂ t)) :
    (∀ t < r.tickRoots.length, (v₁ t).map cellDigest = (v₂ t).map cellDigest) ∨
      Collision (cshake256Bytes tickTag) := by
  by_cases hall : ∀ t < r.tickRoots.length, (v₁ t).map cellDigest = (v₂ t).map cellDigest
  · exact .inl hall
  · obtain ⟨t, ht, ne⟩ : ∃ t, t < r.tickRoots.length ∧ (v₁ t).map cellDigest ≠ (v₂ t).map cellDigest :=
      Classical.byContradiction fun none => hall fun t ht => Classical.byContradiction fun ne => none ⟨t, ht, ne⟩
    have e : vectorRoot (v₁ t) = vectorRoot (v₂ t) := Option.some.inj ((h₁ t ht).symm.trans (h₂ t ht))
    rcases tick_binds e with h | col
    · exact absurd h ne
    · exact .inr col

/-- The same, on the cells themselves: equal vectors at every tick, or one of the two hashes collides. -/
theorem committed_cells_agree_cells (r : EpochRecord) (v₁ v₂ : Nat → List (Cell P))
    (h₁ : ∀ t < r.tickRoots.length, Opens r t (v₁ t)) (h₂ : ∀ t < r.tickRoots.length, Opens r t (v₂ t)) :
    (∀ t < r.tickRoots.length, v₁ t = v₂ t) ∨
      Collision (cshake256Bytes tickTag) ∨ Collision (cshake256Bytes cellTag) := by
  rcases committed_cells_agree r v₁ v₂ h₁ h₂ with hd | col
  · by_cases hall : ∀ t < r.tickRoots.length, v₁ t = v₂ t
    · exact .inl hall
    · obtain ⟨t, ht, ne⟩ : ∃ t, t < r.tickRoots.length ∧ v₁ t ≠ v₂ t :=
        Classical.byContradiction fun none => hall fun t ht => Classical.byContradiction fun ne => none ⟨t, ht, ne⟩
      rcases digests_bind (hd t ht) with h | col
      · exact absurd h ne
      · exact .inr (.inr col)
  · exact .inr (.inl col)

end Commit

section Schedule
variable (sched : Schedule)

/-- The member's check on a downloaded vector (§4, the member's loop, step 2): `n` cells, each under its
position's header. -/
def Shaped (e t : Nat) (v : List (Cell sched.profile)) : Prop :=
  v.map Cell.header = sched.slots.map (sched.headerAt e t)

instance (e t : Nat) (v : List (Cell sched.profile)) : Decidable (Shaped sched e t v) := by
  unfold Shaped; infer_instance

/-- Cell `c` is committed at tick `t` of `r`: some vector that passes the member's check and opens the
committed root holds it. -/
def Included (r : EpochRecord) (t : Nat) (c : Cell sched.profile) : Prop :=
  ∃ v, Opens r t v ∧ Shaped sched r.epoch.toNat t v ∧ c ∈ v

theorem shaped_length {e t : Nat} {v : List (Cell sched.profile)} (h : Shaped sched e t v) :
    v.length = sched.n := by
  have := congrArg List.length h
  simpa [Schedule.slots] using this

theorem shaped_header {e t : Nat} {v : List (Cell sched.profile)} (h : Shaped sched e t v)
    {j : Nat} (hj : j < v.length) : v[j].header = sched.headerAt e t j := by
  have hjn : j < sched.n := shaped_length sched h ▸ hj
  have := congrArg (·[j]?) h
  simpa [List.getElem?_map, hj, Schedule.slots, hjn] using this

theorem headerAt_injective {e t j k : Nat} (hj : j < sched.n) (hk : k < sched.n)
    (h : sched.headerAt e t j = sched.headerAt e t k) : j = k := by
  have := congrArg (fun x => x.slot.val) h
  simp only at this
  rwa [sched.headerAt_slot hj, sched.headerAt_slot hk] at this

/-- One cell per position: in a checked vector, a cell under position `ρ`'s header is the cell at `ρ`. -/
theorem shaped_mem {e t ρ : Nat} {v : List (Cell sched.profile)} {c : Cell sched.profile}
    (h : Shaped sched e t v) (mem : c ∈ v) (hρ : ρ < sched.n) (pos : c.header = sched.headerAt e t ρ) :
    ∃ hρ' : ρ < v.length, v[ρ] = c := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem mem
  have hjn : j < sched.n := shaped_length sched h ▸ hj
  have : j = ρ := headerAt_injective sched hjn hρ ((shaped_header sched h hj).symm.trans pos)
  subst this
  exact ⟨hj, rfl⟩

/-- **`own_omission_evident`.** A member needs no opening to check its own slot: if a cell `c'` under
the header of the cell `c` it sent is committed and differs from `c`, then `c` is not committed (or a
hash collides). One cell per position — whatever the relay is. -/
theorem own_omission_evident (r : EpochRecord) (t : Nat) {c c' : Cell sched.profile}
    (samePos : c'.header = c.header) (incl : Included sched r t c') (differ : c' ≠ c) :
    ¬ Included sched r t c ∨ Collision (cshake256Bytes tickTag) ∨ Collision (cshake256Bytes cellTag) := by
  by_cases hc : Included sched r t c
  · obtain ⟨v₁, o₁, s₁, m₁⟩ := incl
    obtain ⟨v₂, o₂, s₂, m₂⟩ := hc
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem m₁
    have hjn : j < sched.n := shaped_length sched s₁ ▸ hj
    have hpos : c.header = sched.headerAt r.epoch.toNat t j := samePos.symm.trans (shaped_header sched s₁ hj)
    obtain ⟨hj₂, hc₂⟩ := shaped_mem sched s₂ m₂ hjn hpos
    have root : vectorRoot v₁ = vectorRoot v₂ := Option.some.inj (o₁.symm.trans o₂)
    rcases tick_binds root with hd | col
    · have hd' := congrArg (·[j]?) hd
      simp only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj₂,
        Option.map_some, Option.some.injEq] at hd'
      rw [hc₂] at hd'
      rcases cell_binds hd' with he | col
      · exact absurd he differ
      · exact .inr (.inr col)
    · exact .inr (.inl col)
  · exact .inl hc

/-! ### The honest seal: what the relay commits for an epoch -/

/-- The epoch's absent mask, tick-major: position `(t, ρ)` at `t · n + ρ`. -/
def epochMask (prf : FillPrf) (e : Nat) (rx : Nat → List (Submission sched.profile)) : List Bool :=
  (List.range sched.profile.E).flatMap fun t => sched.absentMask prf e t (rx t)

def epochOpening (prf : FillPrf) (e : UInt64) (rx : Nat → List (Submission sched.profile))
    (salt : Digest) : AbsentOpening :=
  ⟨epochMask sched prf e.toNat rx, salt⟩

/-- The relay's record for epoch `e` from what it received each tick (`rx t`): the roots of the
assembled vectors and the commitment to their absent mask. -/
def sealEpoch (prf : FillPrf) (cid : UInt8) (e : UInt64) (rx : Nat → List (Submission sched.profile))
    (salt : Digest) : EpochRecord where
  domain := sched.domain
  epoch := e
  classId := cid
  n := UInt32.ofNat sched.n
  tickRoots := (List.range sched.profile.E).map fun t => vectorRoot (sched.assemble prf e.toNat t (rx t))
  absentCommit := commitAbsent (epochOpening sched prf e rx salt)

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem getElem?_flatMap_range {α : Type} (f : Nat → List α) (n : Nat) (hf : ∀ t, (f t).length = n) :
    ∀ (m t ρ : Nat), t < m → ρ < n → ((List.range m).flatMap f)[t * n + ρ]? = (f t)[ρ]?
  | 0, _, _, ht, _ => absurd ht (Nat.not_lt_zero _)
  | m + 1, t, ρ, ht, hρ => by
    have hlen : ((List.range m).flatMap f).length = m * n := by
      clear ht; induction m with
      | zero => simp
      | succ m ih => simp [List.range_succ, List.flatMap_append, ih, hf, Nat.succ_mul]
    rw [List.range_succ, List.flatMap_append]
    by_cases htm : t < m
    · have hlt : t * n + ρ < m * n :=
        calc t * n + ρ < t * n + n := Nat.add_lt_add_left hρ _
          _ = (t + 1) * n := (Nat.succ_mul t n).symm
          _ ≤ m * n := Nat.mul_le_mul_right n htm
      rw [List.getElem?_append_left (by rw [hlen]; exact hlt)]
      exact getElem?_flatMap_range f n hf m t ρ htm hρ
    · have : t = m := by omega
      subst this
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
      simp

theorem absentMask_getElem? (prf : FillPrf) (e t : Nat) (rx : List (Submission sched.profile))
    {ρ : Nat} (hρ : ρ < sched.n) :
    (sched.absentMask prf e t rx)[ρ]? = some ((sched.assembleAt prf e t rx ρ).2 == .fill) := by
  simp [Schedule.absentMask, Schedule.assembleTagged, Schedule.slots, hρ]

theorem absentMask_length (prf : FillPrf) (e t : Nat) (rx : List (Submission sched.profile)) :
    (sched.absentMask prf e t rx).length = sched.n := by
  simp [Schedule.absentMask, Schedule.assembleTagged, Schedule.slots]

/-- Position `(t, ρ)` of the epoch mask is tick `t`'s mask at `ρ`. -/
theorem epochMask_getElem? (prf : FillPrf) (e : Nat) (rx : Nat → List (Submission sched.profile))
    {t ρ : Nat} (ht : t < sched.profile.E) (hρ : ρ < sched.n) :
    (epochMask sched prf e rx)[t * sched.n + ρ]? = some ((sched.assembleAt prf e t (rx t) ρ).2 == .fill) := by
  unfold epochMask
  rw [getElem?_flatMap_range _ sched.n (fun t => absentMask_length sched prf e t (rx t)) _ t ρ ht hρ,
    absentMask_getElem? sched prf e t (rx t) hρ]

theorem epochMask_length (prf : FillPrf) (e : Nat) (rx : Nat → List (Submission sched.profile)) :
    (epochMask sched prf e rx).length = sched.profile.E * sched.n := by
  unfold epochMask
  generalize sched.profile.E = m
  induction m with
  | zero => simp
  | succ m ih =>
    simp [List.range_succ, List.flatMap_append, ih, absentMask_length, Nat.succ_mul]

theorem assembleAt_fill {prf : FillPrf} {e t : Nat} {rx : List (Submission sched.profile)} {ρ : Nat}
    (h : (sched.assembleAt prf e t rx ρ).2 = .fill) :
    (sched.assembleAt prf e t rx ρ).1 = fillCell sched.profile prf (sched.headerAt e t ρ) := by
  revert h
  unfold Schedule.assembleAt
  split
  · intro h; cases h
  · intro _; rfl

theorem assemble_getElem? (prf : FillPrf) (e t : Nat) (rx : List (Submission sched.profile))
    {ρ : Nat} (hρ : ρ < sched.n) :
    (sched.assemble prf e t rx)[ρ]? = some (sched.assembleAt prf e t rx ρ).1 := by
  simp [Schedule.assemble, Schedule.assembleTagged, Schedule.slots, hρ]

theorem sealEpoch_root (prf : FillPrf) (cid : UInt8) (e : UInt64) (rx : Nat → List (Submission sched.profile))
    (salt : Digest) {t : Nat} (ht : t < sched.profile.E) :
    Opens (sealEpoch sched prf cid e rx salt) t (sched.assemble prf e.toNat t (rx t)) := by
  simp [Opens, sealEpoch, ht]

theorem assemble_shaped (prf : FillPrf) (e t : Nat) (rx : List (Submission sched.profile)) :
    Shaped sched e t (sched.assemble prf e t rx) := by
  simp only [Shaped, Schedule.assemble, Schedule.assembleTagged, List.map_map]
  apply List.map_congr_left
  intro ρ _
  exact sched.assembleAt_header prf e t rx ρ

/-- The relay's own vector is committed: every assembled cell is `Included`. -/
theorem assembled_included (prf : FillPrf) (cid : UInt8) (e : UInt64)
    (rx : Nat → List (Submission sched.profile)) (salt : Digest) {t : Nat} (ht : t < sched.profile.E)
    {c : Cell sched.profile} (mem : c ∈ sched.assemble prf e.toNat t (rx t)) :
    Included sched (sealEpoch sched prf cid e rx salt) t c :=
  ⟨_, sealEpoch_root sched prf cid e rx salt ht, assemble_shaped sched prf e.toNat t (rx t), mem⟩

/-- A position the honest seal marks absent holds exactly the fill (or a hash collides). -/
theorem absent_position_holds_fill (prf : FillPrf) (cid : UInt8) (e : UInt64)
    (rx : Nat → List (Submission sched.profile)) (salt : Digest) {t ρ : Nat}
    (ht : t < sched.profile.E) (hρ : ρ < sched.n)
    (absent : (epochMask sched prf e.toNat rx)[t * sched.n + ρ]? = some true)
    {c : Cell sched.profile} (pos : c.header = sched.headerAt e.toNat t ρ)
    (incl : Included sched (sealEpoch sched prf cid e rx salt) t c) :
    c = fillCell sched.profile prf (sched.headerAt e.toNat t ρ) ∨
      Collision (cshake256Bytes tickTag) ∨ Collision (cshake256Bytes cellTag) := by
  obtain ⟨v, o, sh, m⟩ := incl
  change Shaped sched e.toNat t v at sh
  rw [epochMask_getElem? sched prf e.toNat rx ht hρ] at absent
  have hsrc : (sched.assembleAt prf e.toNat t (rx t) ρ).2 = .fill := by
    simpa using absent
  have hfill := assembleAt_fill sched hsrc
  have root : vectorRoot v = vectorRoot (sched.assemble prf e.toNat t (rx t)) :=
    Option.some.inj (o.symm.trans (sealEpoch_root sched prf cid e rx salt ht))
  obtain ⟨hv, hvc⟩ := shaped_mem sched sh m hρ pos
  rcases tick_binds root with hd | col
  · have hd' := congrArg (·[ρ]?) hd
    simp only [List.getElem?_map, List.getElem?_eq_getElem hv, assemble_getElem? sched prf e.toNat t (rx t) hρ,
      Option.map_some, Option.some.injEq] at hd'
    rw [hvc, hfill] at hd'
    rcases cell_binds hd' with he | col
    · exact .inl he
    · exact .inr (.inr col)
  · exact .inr (.inl col)

/-- **`omission_evident`** (CHANNELS.md §2.4, revision 2). Whoever holds an opening `o` of the honest
seal's `absentCommit` — the operator and the witnesses; no member holds one — learns, at every
position `o` marks absent, that no cell other than the fill is committed there: in particular not the
holder's cell (premise `notFill`: the holder's cell is not byte-equal to the fill). Up to a collision of
one of the three hash instances. The audience is exactly the holders of `o`. -/
theorem omission_evident (prf : FillPrf) (cid : UInt8) (e : UInt64)
    (rx : Nat → List (Submission sched.profile)) (salt : Digest) (o : AbsentOpening)
    (opens : commitAbsent o = (sealEpoch sched prf cid e rx salt).absentCommit)
    {t ρ : Nat} (ht : t < sched.profile.E) (hρ : ρ < sched.n)
    (absent : o.mask[t * sched.n + ρ]? = some true)
    (c : Cell sched.profile) (pos : c.header = sched.headerAt e.toNat t ρ)
    (notFill : c ≠ fillCell sched.profile prf c.header) :
    ¬ Included sched (sealEpoch sched prf cid e rx salt) t c ∨
      Collision (cshake256Bytes absentTag) ∨ Collision (cshake256Bytes tickTag) ∨
      Collision (cshake256Bytes cellTag) := by
  rcases opening_binds (o₂ := epochOpening sched prf e rx salt) opens with hm | col
  · by_cases incl : Included sched (sealEpoch sched prf cid e rx salt) t c
    · have absent' : (epochMask sched prf e.toNat rx)[t * sched.n + ρ]? = some true := by
        rw [← absent, hm]; rfl
      rcases absent_position_holds_fill sched prf cid e rx salt ht hρ absent' pos incl with he | col | col
      · exact absurd (by rw [pos]; exact he) notFill
      · exact .inr (.inr (.inl col))
      · exact .inr (.inr (.inr col))
    · exact .inl incl
  · exact .inr (.inl col)

/-! ### The limit: silence and a drop look the same -/

/-- An execution of one epoch: what each subject emitted per tick, and what was dropped on the way to
the relay (a path adversary or the relay itself; the record cannot tell which). -/
structure Execution (P : Profile) where
  emitted : Nat → List (Submission P)
  dropped : Nat → Submission P → Bool

def Execution.received {P : Profile} (x : Execution P) (t : Nat) : List (Submission P) :=
  (x.emitted t).filter fun s => !x.dropped t s

def Execution.Sent {P : Profile} (x : Execution P) (h : Nat) : Prop := ∃ t c, (h, c) ∈ x.emitted t

/-- Everything the relay publishes for the epoch — record, opening, and every tick's vector — is a
function of what it received. -/
theorem seal_depends_only_on_received (prf : FillPrf) (cid : UInt8) (e : UInt64) (salt : Digest)
    (rx₁ rx₂ : Nat → List (Submission sched.profile)) (same : ∀ t < sched.profile.E, rx₁ t = rx₂ t) :
    sealEpoch sched prf cid e rx₁ salt = sealEpoch sched prf cid e rx₂ salt ∧
      epochOpening sched prf e rx₁ salt = epochOpening sched prf e rx₂ salt ∧
      ∀ t < sched.profile.E, sched.assemble prf e.toNat t (rx₁ t) = sched.assemble prf e.toNat t (rx₂ t) := by
  have hm : epochMask sched prf e.toNat rx₁ = epochMask sched prf e.toNat rx₂ :=
    flatMap_congr_mem fun t ht => by rw [same t (List.mem_range.mp ht)]
  have ho : epochOpening sched prf e rx₁ salt = epochOpening sched prf e rx₂ salt := by
    simp [epochOpening, hm]
  refine ⟨?_, ho, fun t ht => by rw [same t ht]⟩
  simp only [sealEpoch, ho]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [same t (List.mem_range.mp ht)]

end Schedule

/-! ## §9. Opening a record -/

/-- Open a record with an opening's bytes: the mask length is `E · n` of THIS record's class and `n`
(checked on the opening), and the opening must open `absentCommit`. -/
def openRecord (r : EpochRecord) (bytes : List UInt8) : Except OpeningRefusal AbsentOpening :=
  match profileOfId r.classId with
  | none => .error .unknownClass
  | some P =>
    match AbsentOpening.decode P.E r.n.toNat bytes with
    | .error e => .error e
    | .ok o => if commitAbsent o = r.absentCommit then .ok o else .error .notOpening

theorem openRecord_sound {r : EpochRecord} {bytes : List UInt8} {o : AbsentOpening}
    (opened : openRecord r bytes = .ok o) :
    ∃ P, profileOfId r.classId = some P ∧ o.mask.length = P.E * r.n.toNat ∧ o.encode = bytes ∧
      commitAbsent o = r.absentCommit := by
  unfold openRecord at opened
  split at opened
  · cases opened
  · rename_i P hP
    split at opened
    · cases opened
    · rename_i o' hdec
      split at opened
      · rename_i hc
        cases opened
        obtain ⟨henc, hlen⟩ := absentOpening_decode_canonical hdec
        exact ⟨P, hP, hlen, henc, hc⟩
      · cases opened

/-- **A wrong-length opening is refused by name**, against any record of a known class. -/
theorem openRecord_wrong_length_refused {r : EpochRecord} {P : Profile} (cls : profileOfId r.classId = some P)
    {bytes : List UInt8} (wrong : bytes.length ≠ P.E * r.n.toNat + 32) :
    openRecord r bytes = .error .maskLength := by
  simp [openRecord, cls, absentOpening_wrong_length_refused wrong]

/-- The accepting pole: the seal's own opening opens the seal's record. -/
theorem openRecord_epochOpening (sched : Schedule) (prf : FillPrf) (cid : UInt8) (e : UInt64)
    (rx : Nat → List (Submission sched.profile)) (salt : Digest) (cls : profileOfId cid = some sched.profile)
    (nfits : sched.n < 2 ^ 32) :
    openRecord (sealEpoch sched prf cid e rx salt) (epochOpening sched prf e rx salt).encode =
      .ok (epochOpening sched prf e rx salt) := by
  have hn : (UInt32.ofNat sched.n).toNat = sched.n := by simp; omega
  have hlen : (epochOpening sched prf e rx salt).mask.length = sched.profile.E * sched.n :=
    epochMask_length sched prf e.toNat rx
  simp only [openRecord, sealEpoch, cls, hn]
  rw [absentOpening_decode_encode _ _ _ hlen]
  simp

/-! ## §10. Equivocation: transferable outside a Store, impossible inside one -/

/-- A signature check anyone can run: `verify key message signature`. -/
abbrev Verify := List UInt8 → List UInt8 → List UInt8 → Bool

/-- What the sequencer signs when it hands a record to a witness (outside the kernel, where the
append's signed command does not travel). -/
def signingBytes (r : EpochRecord) : List UInt8 := sigTag ++ r.encode

/-- Two records for one (domain, epoch), signed under one key. -/
structure Equivocation where
  key : List UInt8
  first : EpochRecord
  second : EpochRecord
  sigFirst : List UInt8
  sigSecond : List UInt8
  deriving DecidableEq

/-- The check anyone re-runs on the object: same (domain, epoch), different records, both verify. -/
def Equivocation.check (verify : Verify) (q : Equivocation) : Bool :=
  q.first.domain == q.second.domain && q.first.epoch == q.second.epoch && q.first != q.second &&
    verify q.key (signingBytes q.first) q.sigFirst && verify q.key (signingBytes q.second) q.sigSecond

/-- **`relay_equivocation_transferable`.** Two records for the same (domain, epoch) with different
tick roots, both signed under the sequencer's key, make an `Equivocation` whose check passes for anyone
holding the key — a value a third party re-verifies with no access to the domain. (That it is evidence
*against the sequencer* is the signature's unforgeability, outside this file.) -/
theorem relay_equivocation_transferable (verify : Verify) (key : List UInt8) (r₁ r₂ : EpochRecord)
    (s₁ s₂ : List UInt8) (sameKey : r₁.domain = r₂.domain ∧ r₁.epoch = r₂.epoch)
    (diff : r₁.tickRoots ≠ r₂.tickRoots)
    (v₁ : verify key (signingBytes r₁) s₁ = true) (v₂ : verify key (signingBytes r₂) s₂ = true) :
    Equivocation.check verify ⟨key, r₁, r₂, s₁, s₂⟩ = true := by
  have hne : r₁ ≠ r₂ := fun h => diff (by rw [h])
  simp [Equivocation.check, sameKey.1, sameKey.2, hne, v₁, v₂]

/-- The check is sound: a passing object is two different signed records for one (domain, epoch). -/
theorem equivocation_check_sound (verify : Verify) (q : Equivocation) (ok : q.check verify = true) :
    q.first.domain = q.second.domain ∧ q.first.epoch = q.second.epoch ∧ q.first ≠ q.second ∧
      verify q.key (signingBytes q.first) q.sigFirst = true ∧
      verify q.key (signingBytes q.second) q.sigSecond = true := by
  simp only [Equivocation.check, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at ok
  exact ⟨ok.1.1.1.1, ok.1.1.1.2, ok.1.1.2, ok.1.2, ok.2⟩

/-- The refuting pole: an object with an unverifiable signature is refused. -/
theorem equivocation_unsigned_refused (verify : Verify) (q : Equivocation)
    (bad : verify q.key (signingBytes q.second) q.sigSecond = false) : q.check verify = false := by
  simp [Equivocation.check, bad]

/-- And the same record twice is no equivocation. -/
theorem equivocation_same_record_refused (verify : Verify) (key : List UInt8) (r : EpochRecord)
    (s₁ s₂ : List UInt8) : Equivocation.check verify ⟨key, r, r, s₁, s₂⟩ = false := by
  simp [Equivocation.check]

/-! ## §11. Instances and poles on concrete values -/

namespace Example

open Minidregg.Theory.Channel.Example (sched prf cellAt received)

def zero32 : Digest := ⟨List.replicate 32 0, by decide⟩

/-- A P1 record of domain 7, `n = 3`, at epoch `e`, with `k` roots. -/
def record (e : UInt64) (k : Nat) : EpochRecord := ⟨⟨7, by decide⟩, e, 1, 3, List.replicate k zero32, zero32⟩

theorem record_size : (record 5 16).encode.length = 559 := by rw [epochRecord_size]; rfl

theorem opening_wrong_length_refused : openRecord (record 5 16) (List.replicate 79 0) = .error .maskLength := rfl
theorem opening_long_refused : openRecord (record 5 16) (List.replicate 81 0) = .error .maskLength := rfl
theorem opening_byte_refused :
    AbsentOpening.decode 16 3 (2 :: List.replicate 79 0) = .error .maskByte := rfl

/-- Holder 10 (slot 0) is silent at tick 3 of epoch 1; holder 11's cell arrives (`received`). -/
def rx : Nat → List (Submission sched.profile) := fun t => if t = 3 then received else []

def e1 : UInt64 := 1

theorem silent_slot_marked : (epochMask sched prf e1.toNat rx)[3 * sched.n + 0]? = some true := by
  rw [epochMask_getElem? sched prf _ rx (by decide) (by decide)]
  decide +kernel

/-- What holder 10 would have sent at tick 3. -/
def mine : Cell sched.profile := cellAt 0 0x10

theorem mine_not_fill : mine ≠ fillCell sched.profile prf mine.header := by decide +kernel

/-- **`omission_evident`, satisfiable**: every premise is discharged on a real seal. -/
theorem omission_evident_instance :
    ¬ Included sched (sealEpoch sched prf 1 e1 rx zero32) 3 mine ∨
      Collision (cshake256Bytes absentTag) ∨ Collision (cshake256Bytes tickTag) ∨
      Collision (cshake256Bytes cellTag) :=
  omission_evident sched prf 1 e1 rx zero32 (epochOpening sched prf e1 rx zero32) rfl (by decide) (by decide)
    silent_slot_marked mine (by decide +kernel) mine_not_fill

/-- Holder 11's cell at slot 1. -/
def theirs : Cell sched.profile := cellAt 1 0x11

theorem theirs_included : Included sched (sealEpoch sched prf 1 e1 rx zero32) 3 theirs :=
  assembled_included sched prf 1 e1 rx zero32 (by decide) (by decide +kernel)

/-- **The opening premise is load-bearing**: a mask that does not open the commitment can mark absent
a position that holds the holder's (non-fill) cell. -/
theorem forged_mask_marks_included :
    (⟨List.replicate 48 true, zero32⟩ : AbsentOpening).mask[3 * sched.n + 1]? = some true ∧
      theirs.header = sched.headerAt e1.toNat 3 1 ∧ theirs ≠ fillCell sched.profile prf theirs.header ∧
      Included sched (sealEpoch sched prf 1 e1 rx zero32) 3 theirs :=
  ⟨by decide, by decide +kernel, by decide +kernel, theirs_included⟩

/-- **`notFill` is load-bearing**: at the absent slot 0 the fill itself is committed. -/
theorem fill_included_at_absent :
    (epochMask sched prf e1.toNat rx)[3 * sched.n + 0]? = some true ∧
      Included sched (sealEpoch sched prf 1 e1 rx zero32) 3 (fillCell sched.profile prf (sched.headerAt 1 3 0)) :=
  ⟨silent_slot_marked, assembled_included sched prf 1 e1 rx zero32 (by decide) (by decide +kernel)⟩

/-- **`own_omission_evident`, satisfiable**: holder 10 sent `mine`; the fill is committed at its
position, so `mine` is not (up to a collision) — without any opening. -/
theorem own_omission_evident_instance :
    ¬ Included sched (sealEpoch sched prf 1 e1 rx zero32) 3 mine ∨
      Collision (cshake256Bytes tickTag) ∨ Collision (cshake256Bytes cellTag) :=
  own_omission_evident sched _ 3 (c' := fillCell sched.profile prf (sched.headerAt 1 3 0))
    (by decide +kernel) fill_included_at_absent.2 (by decide +kernel)

/-- **The member's shape check is load-bearing**: a record whose committed vector holds two cells under
one header (a relay's malformed vector) opens to both, if the member skips the check. -/
def twoAtOne : List (Cell sched.profile) := [cellAt 0 0x10, cellAt 0 0x20, cellAt 2 0]

def malformedRecord : EpochRecord := ⟨⟨7, by decide⟩, 1, 1, 3, [vectorRoot twoAtOne], zero32⟩

theorem unshaped_opens_both :
    Opens malformedRecord 0 twoAtOne ∧ cellAt 0 0x10 ∈ twoAtOne ∧ cellAt 0 0x20 ∈ twoAtOne ∧
      (cellAt 0 0x10).header = (cellAt 0 0x20).header ∧ cellAt 0 0x10 ≠ cellAt 0 0x20 ∧
      ¬ Shaped sched 1 0 twoAtOne :=
  ⟨rfl, by decide +kernel, by decide +kernel, rfl, by decide +kernel, by decide +kernel⟩

/-- **`committed_cells_agree`, satisfiable**: two holders of the seal with its own vectors. -/
theorem committed_cells_agree_instance :
    (∀ t < (sealEpoch sched prf 1 e1 rx zero32).tickRoots.length,
        (sched.assemble prf 1 t (rx t)).map cellDigest = (sched.assemble prf 1 t (rx t)).map cellDigest) ∨
      Collision (cshake256Bytes tickTag) := by
  have h : ∀ t < (sealEpoch sched prf 1 e1 rx zero32).tickRoots.length,
      Opens (sealEpoch sched prf 1 e1 rx zero32) t (sched.assemble prf 1 t (rx t)) := by
    intro t ht
    simp only [sealEpoch, List.length_map, List.length_range] at ht
    exact sealEpoch_root sched prf 1 e1 rx zero32 ht
  exact committed_cells_agree _ _ _ h h

/-- Its pole: holders of DIFFERENT records hold different cells (the record is what they share). -/
theorem different_records_different_vectors :
    sched.assemble prf 1 3 (rx 3) ≠ sched.assemble prf 1 3 [] := by decide +kernel

/-- **`silent_and_dropped_indistinguishable`.** Holder 10 is silent in one execution and sends `mine`
in the other, where it is dropped before the relay. The record, the opening and every tick's vector are
identical, and both mark slot 0 absent: from the record alone (and from the opening), silence and a
drop are the same mark. -/
def silent : Execution sched.profile := ⟨fun _ => [], fun _ _ => false⟩
def droppedPath : Execution sched.profile := ⟨fun _ => [(10, mine)], fun _ _ => true⟩

theorem silent_and_dropped_indistinguishable :
    ¬ silent.Sent 10 ∧ droppedPath.Sent 10 ∧
      sealEpoch sched prf 1 e1 silent.received zero32 = sealEpoch sched prf 1 e1 droppedPath.received zero32 ∧
      epochOpening sched prf e1 silent.received zero32 = epochOpening sched prf e1 droppedPath.received zero32 ∧
      (∀ t < sched.profile.E,
        sched.assemble prf e1.toNat t (silent.received t) = sched.assemble prf e1.toNat t (droppedPath.received t)) ∧
      (epochOpening sched prf e1 silent.received zero32).mask[3 * sched.n + 0]? = some true := by
  have same : ∀ t < sched.profile.E, silent.received t = droppedPath.received t := by
    intro t _; simp [Execution.received, silent, droppedPath]
  obtain ⟨hs, ho, hv⟩ := seal_depends_only_on_received sched prf 1 e1 zero32 _ _ same
  refine ⟨?_, ⟨0, mine, by simp [droppedPath]⟩, hs, ho, hv, ?_⟩
  · rintro ⟨t, c, h⟩; simp [silent] at h
  · show (epochMask sched prf e1.toNat silent.received)[3 * sched.n + 0]? = some true
    rw [epochMask_getElem? sched prf _ _ (by decide) (by decide)]
    decide +kernel

/-- The seal's own opening opens it (the accepting pole of `openRecord`). -/
theorem seal_opens : openRecord (sealEpoch sched prf 1 e1 rx zero32) (epochOpening sched prf e1 rx zero32).encode =
    .ok (epochOpening sched prf e1 rx zero32) :=
  openRecord_epochOpening sched prf 1 e1 rx zero32 rfl (by decide)

end Example


end Minidregg.Kernel.DomainEpoch
