/-
# Kernel.DomainEpochExport — the relay's byte entry points for the epoch (CHANNELS.md §2.4, §9 row 9)

CH-CELL exported the cell codec, `assemble` and `fanout`; CH-EPOCH defined the record, the opening, the
absent commitment and the honest seal, with no byte entry point. This module adds them, so the native
relay (`mini relay`, `native/resource-client/src/relay.rs`) links the kernel's own definitions and never
re-implements cSHAKE256 framing, the tick root, the record codec or the opening:

| symbol | function | tied to the definition by |
|---|---|---|
| `minidregg_channel_profile` | `profileBytes` | `profileBytesList_is_profile` |
| `minidregg_channel_header` | `headerBytes` | `headerBytesList_is_headerAt` |
| `minidregg_channel_tick_root` | `tickRootBytes` | `tickRootBytesList_is_vectorRoot`, `tickRoot_of_assemble` |
| `minidregg_channel_seal` | `sealBytes` | `sealBytesList_is_sealEpoch`, `relay_pipeline_is_sealEpoch` |
| `minidregg_channel_commit_absent` | `commitAbsentBytes` | `commitAbsentBytesList_is_commitAbsent` |
| `minidregg_channel_open` | `openBytes` | `openBytesList_is_openRecord`, `sealed_opening_opens` |
| `minidregg_channel_topic` | `topicBytes` | `topicBytesList_is_recordAppend` (in `Kernel.DomainEpochAudit`) |

`relay_pipeline_is_sealEpoch` is the end-to-end statement: the seal export, fed the `E` outputs of the
assemble export for one epoch, returns exactly `(sealEpoch …).encode ++ (epochOpening …).encode` for
the schedule, fill and received cells those byte calls denote. The fill is one PRF stream per tick
(`pads t`); as a `FillPrf` it reads the stream of the header's tick.

Every theorem is `#assert_axioms`-clean (at most `propext`, `Classical.choice`, `Quot.sound`); the pins
are in `Kernel.DomainEpochAudit`, so this module's import closure — the closure `channel-lib/build.sh`
links into every relay, member and witness — has no Mathlib. `topicBytesList_is_recordAppend` relates
the topic export to the kernel's `recordAppend` (`Kernel.DomainEpochLaw`), so it is stated there too. No
statement evaluates the hash: binding is CH-EPOCH's `Collision` carrier, not restated here.
-/
import Kernel.DomainEpoch
import Theory.Channel.Envelope

namespace Minidregg.Kernel.DomainEpochExport

open Minidregg.Theory.Channel
open Minidregg.Kernel.DomainEpoch

set_option autoImplicit false

/-! ## §1. Slicing fixed-width records -/

/-- `k` consecutive `w`-byte slices of a byte string (structural on `k`). -/
def slices (w : Nat) : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | k + 1, bytes => bytes.take w :: slices w k (bytes.drop w)

theorem slices_flatMap {α : Type} {w : Nat} (f : α → List UInt8) (hf : ∀ a, (f a).length = w) :
    ∀ (xs : List α) (rest : List UInt8), slices w xs.length (xs.flatMap f ++ rest) = xs.map f
  | [], _ => rfl
  | a :: xs, rest => by
    simp only [slices, List.flatMap_cons, List.append_assoc, List.map_cons]
    rw [List.take_left' (hf a), List.drop_left' (hf a), slices_flatMap f hf xs rest]

theorem length_flatMap_const {α : Type} {w : Nat} (f : α → List UInt8) (hf : ∀ a, (f a).length = w) :
    ∀ xs : List α, (xs.flatMap f).length = xs.length * w
  | [] => by simp
  | a :: xs => by
    simp only [List.flatMap_cons, List.length_append, hf a, length_flatMap_const f hf xs, List.length_cons,
      Nat.add_mul, Nat.one_mul] <;> omega

theorem U16.ofNat_val (d : U16) : U16.ofNat d.val = d := Fin.ext (Nat.mod_eq_of_lt d.isLt)

/-! ## §2. The class, on bytes -/

/-- `C 4 | rate mHz 4 | E 4 | δ 4 | δ_relay 4 | μ 4`, big-endian; empty for an unknown class. The relay
reads its timing and sizes from here, never from a Rust constant. -/
def profileBytesList (pid : UInt8) : List UInt8 :=
  match profileOfId pid with
  | none => []
  | some P => beBytes 4 P.C ++ beBytes 4 P.rateMilliHz ++ beBytes 4 P.E ++ beBytes 4 P.deltaMs ++
      beBytes 4 P.deltaRelayMs ++ beBytes 4 P.muMs

@[export minidregg_channel_profile]
def profileBytes (pid : UInt8) : ByteArray := ⟨(profileBytesList pid).toArray⟩

theorem profileBytesList_is_profile {pid : UInt8} {P : Profile} (hp : profileOfId pid = some P) :
    profileBytesList pid = beBytes 4 P.C ++ beBytes 4 P.rateMilliHz ++ beBytes 4 P.E ++ beBytes 4 P.deltaMs ++
      beBytes 4 P.deltaRelayMs ++ beBytes 4 P.muMs := by
  simp [profileBytesList, hp]

theorem profileBytesList_refuses {pid : UInt8} (hp : profileOfId pid = none) : profileBytesList pid = [] := by
  simp [profileBytesList, hp]

/-! ## §3. A position's header -/

/-- The header of position `(epoch, tick, slot)` of domain `domain`, 8 bytes (`Schedule.headerAt`'s
encoding: each field mod 2¹⁶). An emitter builds its cell's header here. -/
def headerBytesList (domain epoch tick slot : Nat) : List UInt8 :=
  (Header.mk (U16.ofNat domain) (U16.ofNat epoch) (U16.ofNat tick) (U16.ofNat slot)).encode

@[export minidregg_channel_header]
def headerBytes (domain : UInt16) (epoch : UInt64) (tick slot : UInt32) : ByteArray :=
  ⟨(headerBytesList domain.toNat epoch.toNat tick.toNat slot.toNat).toArray⟩

theorem headerBytesList_is_headerAt (sched : Schedule) (e t ρ : Nat) :
    headerBytesList sched.domain.val e t ρ = (sched.headerAt e t ρ).encode := by
  simp [headerBytesList, Schedule.headerAt, U16.ofNat_val]

/-! ## §4. The tick root of an assembled vector -/

/-- What one call of `minidregg_channel_assemble` returns, as the definitions denote it: the vector's
cells then its absent mask (`1` = filled). -/
def tickOut (sched : Schedule) (prf : FillPrf) (e t : Nat) (rx : List (Submission sched.profile)) :
    List UInt8 :=
  (sched.assemble prf e t rx).flatMap Cell.encode ++ (sched.absentMask prf e t rx).map bit

/-- The root of an `n`-cell vector given as `n · C` bytes: each cell's digest (`cellDigest` hashes the
cell's encoding), then `tickRoot`. -/
def rootOfCells (P : Profile) (n : Nat) (cells : List UInt8) : Digest :=
  tickRoot ((slices P.C n cells).map (hashWith cellTag))

def tickRootBytesList (pid : UInt8) (n : Nat) (cells : List UInt8) : List UInt8 :=
  match profileOfId pid with
  | none => []
  | some P => if cells.length = n * P.C then (rootOfCells P n cells).val else []

@[export minidregg_channel_tick_root]
def tickRootBytes (pid : UInt8) (n : UInt32) (cells : ByteArray) : ByteArray :=
  ⟨(tickRootBytesList pid n.toNat cells.toList).toArray⟩

theorem rootOfCells_vector {P : Profile} (v : List (Cell P)) (rest : List UInt8) :
    rootOfCells P v.length (v.flatMap Cell.encode ++ rest) = vectorRoot v := by
  simp only [rootOfCells, slices_flatMap Cell.encode cell_size_exact v rest, List.map_map, vectorRoot]
  rfl

/-- **The tick-root export is `vectorRoot`.** -/
theorem tickRootBytesList_is_vectorRoot {pid : UInt8} {P : Profile} (hp : profileOfId pid = some P)
    (v : List (Cell P)) : tickRootBytesList pid v.length (v.flatMap Cell.encode) = (vectorRoot v).val := by
  have hl : (v.flatMap Cell.encode).length = v.length * P.C := length_flatMap_const _ cell_size_exact v
  simp only [tickRootBytesList, hp, hl, if_true]
  have := rootOfCells_vector v []
  rw [List.append_nil] at this
  rw [this]

/-- The refusing pole: a cell stream that is not `n · C` bytes has no root. -/
theorem tickRootBytesList_refuses_length {pid : UInt8} {P : Profile} (hp : profileOfId pid = some P)
    {n : Nat} {cells : List UInt8} (h : cells.length ≠ n * P.C) : tickRootBytesList pid n cells = [] := by
  simp [tickRootBytesList, hp, h]

theorem tickOut_length (sched : Schedule) (prf : FillPrf) (e t : Nat) (rx : List (Submission sched.profile)) :
    (tickOut sched prf e t rx).length = sched.n * (sched.profile.C + 1) := by
  have hl := length_flatMap_const Cell.encode (cell_size_exact (P := sched.profile)) (sched.assemble prf e t rx)
  simp only [tickOut, List.length_append, hl, sched.assemble_length, List.length_map,
    absentMask_length, Nat.mul_add, Nat.mul_one] <;> omega

/-- The root the relay computes over an assemble output's cell part is the assembled vector's root. -/
theorem tickRoot_of_assemble (sched : Schedule) (prf : FillPrf) (e t : Nat) (rx : List (Submission sched.profile)) :
    rootOfCells sched.profile sched.n (tickOut sched prf e t rx) = vectorRoot (sched.assemble prf e t rx) := by
  have := rootOfCells_vector (sched.assemble prf e t rx) ((sched.absentMask prf e t rx).map bit)
  rw [sched.assemble_length] at this
  exact this

/-! ## §5. The assemble export denotes `tickOut` -/

/-- The schedule `minidregg_channel_assemble` builds from its lease records. -/
def bytesSchedule (P : Profile) (domain n : Nat) (hn : n ≤ 65536) (ls : List (List UInt8)) : Schedule :=
  ⟨U16.ofNat domain, P, n, ls.map (parseLease (U16.ofNat domain) P), hn⟩

/-- The fill it reads: position `ρ`'s slice of the tick's PRF stream. -/
def padPrf (P : Profile) (pad : List UInt8) : FillPrf :=
  fun h => (pad.drop (h.slot.val * P.bodyLen)).take P.bodyLen

/-- The submissions it reads from its received records (`sender 8 | cell C`). -/
def bytesReceived (sched : Schedule) (rs : List (List UInt8)) : List (Submission sched.profile) :=
  rs.filterMap fun r => (Cell.decode sched.profile (r.drop 8)).map fun c => (readBE (r.take 8), c)

/-- **The assemble export is `tickOut`** over the schedule, fill and submissions its bytes denote. -/
theorem assembleBytesList_is_tickOut {pid : UInt8} {P : Profile} (hp : profileOfId pid = some P)
    {domain n epoch tick : Nat} (hn : n ≤ 65536) {leaseBytes receivedBytes pad : List UInt8}
    {ls rs : List (List UInt8)} (hls : records 28 leaseBytes = some ls)
    (hrs : records (8 + P.C) receivedBytes = some rs) :
    assembleBytesList pid domain n epoch tick leaseBytes receivedBytes pad =
      tickOut (bytesSchedule P domain n hn ls) (padPrf P pad) epoch tick
        (bytesReceived (bytesSchedule P domain n hn ls) rs) := by
  simp only [assembleBytesList, hp, dif_pos hn, hls, hrs, tickOut, Schedule.assemble, Schedule.absentMask,
    List.flatMap_map, List.map_map]
  congr 1

/-- Assembly at tick `t` reads the fill only at tick `t`'s positions. -/
theorem tickOut_prf_congr (sched : Schedule) {prf₁ prf₂ : FillPrf} (e t : Nat) (rx : List (Submission sched.profile))
    (h : ∀ ρ, prf₁ (sched.headerAt e t ρ) = prf₂ (sched.headerAt e t ρ)) :
    tickOut sched prf₁ e t rx = tickOut sched prf₂ e t rx := by
  have hat : ∀ ρ, sched.assembleAt prf₁ e t rx ρ = sched.assembleAt prf₂ e t rx ρ := by
    intro ρ
    unfold Schedule.assembleAt
    split
    · rfl
    · simp only [fillCell, h]
  have hf : sched.assembleAt prf₁ e t rx = sched.assembleAt prf₂ e t rx := funext hat
  simp only [tickOut, Schedule.assemble, Schedule.absentMask, Schedule.assembleTagged, hf]

/-! ## §6. The seal -/

/-- The absent opening the seal publishes from mask bytes and a salt. -/
def openingOf (mask salt : List UInt8) : AbsentOpening := ⟨mask.map (· == 1), fit 32 salt⟩

/-- The record the seal publishes. -/
def recordOf (pid : UInt8) (domain n epoch : Nat) (roots : List Digest) (o : AbsentOpening) : EpochRecord :=
  { domain := U16.ofNat domain, epoch := UInt64.ofNat epoch, classId := pid, n := UInt32.ofNat n,
    tickRoots := roots, absentCommit := commitAbsent o }

/-- The `E` per-tick assemble outputs of an epoch, each `n · (C + 1)` bytes. -/
def tickPieces (P : Profile) (n : Nat) (ticks : List UInt8) : List (List UInt8) :=
  slices (n * (P.C + 1)) P.E ticks

/-- The epoch's mask bytes, tick-major: each piece after its `n · C` cell bytes. -/
def piecesMask (P : Profile) (n : Nat) (pieces : List (List UInt8)) : List UInt8 :=
  pieces.flatMap fun o => o.drop (n * P.C)

/-- **The relay's seal on bytes.** In: the class, the domain, `n`, the channel epoch, the concatenated
outputs of `minidregg_channel_assemble` for ticks `0 … E − 1`, and the 32-byte salt. Out: the record's
encoding, then the opening's (`47 + 32E` and `E · n + 32` bytes, `sealBytesList_length`). Empty = refused:
an unknown class, `n > 2¹⁶`, a wrong length, or a mask byte other than `0`/`1`. -/
def sealBytesList (pid : UInt8) (domain n epoch : Nat) (ticks salt : List UInt8) : List UInt8 :=
  match profileOfId pid with
  | none => []
  | some P =>
    if n ≤ 65536 ∧ ticks.length = P.E * (n * (P.C + 1)) ∧ salt.length = 32 ∧
        (piecesMask P n (tickPieces P n ticks)).all (· ≤ 1) = true then
      (recordOf pid domain n epoch ((tickPieces P n ticks).map (rootOfCells P n))
          (openingOf (piecesMask P n (tickPieces P n ticks)) salt)).encode ++
        (openingOf (piecesMask P n (tickPieces P n ticks)) salt).encode
    else []

@[export minidregg_channel_seal]
def sealBytes (pid : UInt8) (domain : UInt16) (n : UInt32) (epoch : UInt64) (ticks salt : ByteArray) : ByteArray :=
  ⟨(sealBytesList pid domain.toNat n.toNat epoch.toNat ticks.toList salt.toList).toArray⟩

theorem map_beq_one_bit (bs : List Bool) : (bs.map bit).map (· == 1) = bs := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id bs]
  apply List.map_congr_left
  intro b _
  cases b <;> rfl

theorem all_bit_le_one (bs : List Bool) : (bs.map bit).all (· ≤ 1) = true := by
  simp only [List.all_map, List.all_eq_true, Function.comp]
  intro b _
  cases b <;> decide

/-- **The seal export is the honest seal.** Fed the epoch's per-tick `tickOut`s (what the assemble
export returns, `assembleBytesList_is_tickOut`) and the salt, it returns the encodings of
`sealEpoch` and `epochOpening`. -/
theorem sealBytesList_is_sealEpoch (sched : Schedule) (prf : FillPrf) {cid : UInt8}
    (hp : profileOfId cid = some sched.profile) (e : UInt64) (rx : Nat → List (Submission sched.profile))
    (salt : Digest) :
    sealBytesList cid sched.domain.val sched.n e.toNat
        ((List.range sched.profile.E).flatMap fun t => tickOut sched prf e.toNat t (rx t)) salt.val =
      (sealEpoch sched prf cid e rx salt).encode ++ (epochOpening sched prf e rx salt).encode := by
  have hw : ∀ t, (tickOut sched prf e.toNat t (rx t)).length = sched.n * (sched.profile.C + 1) :=
    fun t => tickOut_length sched prf e.toNat t (rx t)
  have hlen := length_flatMap_const (fun t => tickOut sched prf e.toNat t (rx t)) hw (List.range sched.profile.E)
  rw [List.length_range] at hlen
  have hpieces : tickPieces sched.profile sched.n
      ((List.range sched.profile.E).flatMap fun t => tickOut sched prf e.toNat t (rx t)) =
      (List.range sched.profile.E).map fun t => tickOut sched prf e.toNat t (rx t) := by
    have := slices_flatMap (fun t => tickOut sched prf e.toNat t (rx t)) hw (List.range sched.profile.E) []
    rw [List.append_nil, List.length_range] at this
    exact this
  have hcells : ∀ t, ((sched.assemble prf e.toNat t (rx t)).flatMap Cell.encode).length =
      sched.n * sched.profile.C := by
    intro t
    rw [length_flatMap_const Cell.encode cell_size_exact, sched.assemble_length]
  have hmask : piecesMask sched.profile sched.n
      ((List.range sched.profile.E).map fun t => tickOut sched prf e.toNat t (rx t)) =
      (epochMask sched prf e.toNat rx).map bit := by
    simp only [piecesMask, epochMask, List.flatMap_map, List.map_flatMap]
    apply flatMap_congr_mem
    intro t _
    exact List.drop_left' (hcells t)
  have hroots : ((List.range sched.profile.E).map fun t => tickOut sched prf e.toNat t (rx t)).map
      (rootOfCells sched.profile sched.n) =
      (List.range sched.profile.E).map fun t => vectorRoot (sched.assemble prf e.toNat t (rx t)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro t _
    exact tickRoot_of_assemble sched prf e.toNat t (rx t)
  have hopen : openingOf ((epochMask sched prf e.toNat rx).map bit) salt.val = epochOpening sched prf e rx salt := by
    simp only [openingOf, epochOpening, map_beq_one_bit]
    congr 1
    exact Blob.ext (fit_val_of_length _ salt.property)
  have hcond : sched.n ≤ 65536 ∧
      ((List.range sched.profile.E).flatMap fun t => tickOut sched prf e.toNat t (rx t)).length =
        sched.profile.E * (sched.n * (sched.profile.C + 1)) ∧ salt.val.length = 32 ∧
      (piecesMask sched.profile sched.n (tickPieces sched.profile sched.n
        ((List.range sched.profile.E).flatMap fun t => tickOut sched prf e.toNat t (rx t)))).all (· ≤ 1) = true := by
    refine ⟨sched.slotsFit, hlen, salt.property, ?_⟩
    rw [hpieces, hmask]
    exact all_bit_le_one _
  simp only [sealBytesList, hp, if_pos hcond]
  rw [hpieces, hmask, hroots, hopen]
  simp only [recordOf, sealEpoch, U16.ofNat_val, UInt64.ofNat_toNat]

/-- The seal output's length, whenever it does not refuse. -/
theorem sealBytesList_length {pid : UInt8} {P : Profile} (hp : profileOfId pid = some P)
    {domain n epoch : Nat} {ticks salt : List UInt8} (ne : sealBytesList pid domain n epoch ticks salt ≠ []) :
    (sealBytesList pid domain n epoch ticks salt).length = (47 + 32 * P.E) + (P.E * n + 32) := by
  unfold sealBytesList at ne ⊢
  simp only [hp] at ne ⊢
  split
  · rename_i h
    obtain ⟨_, hl, hs, _⟩ := h
    have hk : (tickPieces P n ticks).length = P.E := by
      have : ∀ (k : Nat) (b : List UInt8) (w : Nat), (slices w k b).length = k := by
        intro k; induction k with
        | zero => intro b w; rfl
        | succ k ih => intro b w; simp [slices, ih]
      exact this _ _ _
    have hm : (piecesMask P n (tickPieces P n ticks)).length = P.E * n := by
      have hpl : ∀ o ∈ tickPieces P n ticks, (o.drop (n * P.C)).length = n := by
        -- each piece is a `n · (C + 1)`-byte slice of a string of exactly `E` such slices
        have hsl : ∀ (k : Nat) (b : List UInt8), b.length = k * (n * (P.C + 1)) →
            ∀ o ∈ slices (n * (P.C + 1)) k b, o.length = n * (P.C + 1) := by
          intro k; induction k with
          | zero => intro b _ o ho; simp [slices] at ho
          | succ k ih =>
            intro b hb o ho
            simp only [slices, List.mem_cons] at ho
            rcases ho with rfl | ho
            · simp only [List.length_take]; rw [hb]; rw [Nat.succ_mul]; omega
            · exact ih _ (by simp only [List.length_drop, hb]; rw [Nat.succ_mul]; omega) o ho
        intro o ho
        have := hsl P.E ticks (by rw [hl]) o ho
        simp only [List.length_drop, this]
        rw [Nat.mul_add, Nat.mul_one]; omega
      unfold piecesMask
      rw [List.length_flatMap]
      rw [List.map_congr_left (fun o ho => hpl o ho), List.map_const', List.sum_replicate_nat, hk]
    simp only [List.length_append, epochRecord_size, recordOf, List.length_map, hk, openingOf,
      AbsentOpening.encode, List.length_map, hm, (fit 32 salt).property]
  · rename_i h
    simp only [h, if_false] at ne
    exact absurd rfl ne

/-- The refusing pole: a tick stream of the wrong length seals nothing. -/
theorem sealBytesList_refuses_length {pid : UInt8} {P : Profile} (hp : profileOfId pid = some P)
    {domain n epoch : Nat} {ticks salt : List UInt8} (h : ticks.length ≠ P.E * (n * (P.C + 1))) :
    sealBytesList pid domain n epoch ticks salt = [] := by
  simp [sealBytesList, hp, h]

/-- **The relay's whole epoch pipeline is the honest seal.** The relay calls the assemble export once per
tick `t < E` with the domain's lease records, the records it received for `t` (`rxBytes t`) and the
tick's fill stream (`pads t`), then the seal export on the concatenated outputs and a salt. The result
is the encoding of `sealEpoch` and `epochOpening` for the schedule those lease bytes denote, the fill
that reads tick `t`'s stream at tick `t`, and the cells those received records denote. -/
theorem relay_pipeline_is_sealEpoch {pid : UInt8} {P : Profile} (hp : profileOfId pid = some P)
    {domain n : Nat} (hn : n ≤ 65536) (hd : domain < 65536) {leaseBytes : List UInt8} {ls : List (List UInt8)}
    (hls : records 28 leaseBytes = some ls) (e : UInt64) (rxBytes pads : Nat → List UInt8)
    (rs : Nat → List (List UInt8)) (hrs : ∀ t, records (8 + P.C) (rxBytes t) = some (rs t)) (salt : Digest) :
    sealBytesList pid domain n e.toNat
        ((List.range P.E).flatMap fun t => assembleBytesList pid domain n e.toNat t leaseBytes (rxBytes t) (pads t))
        salt.val =
      (sealEpoch (bytesSchedule P domain n hn ls) (fun h => padPrf P (pads h.tick.val) h) pid e
          (fun t => bytesReceived (bytesSchedule P domain n hn ls) (rs t)) salt).encode ++
        (epochOpening (bytesSchedule P domain n hn ls) (fun h => padPrf P (pads h.tick.val) h) e
          (fun t => bytesReceived (bytesSchedule P domain n hn ls) (rs t)) salt).encode := by
  have hE := P.epochFits
  have step : ∀ t ∈ List.range P.E,
      assembleBytesList pid domain n e.toNat t leaseBytes (rxBytes t) (pads t) =
        tickOut (bytesSchedule P domain n hn ls) (fun h => padPrf P (pads h.tick.val) h) e.toNat t
          (bytesReceived (bytesSchedule P domain n hn ls) (rs t)) := by
    intro t ht
    have htE : t < 65536 := Nat.lt_of_lt_of_le (List.mem_range.mp ht) hE.2
    rw [assembleBytesList_is_tickOut hp hn hls (hrs t)]
    apply tickOut_prf_congr
    intro ρ
    simp only [Schedule.headerAt, U16.ofNat_val_of_lt htE]
  rw [flatMap_congr_mem step]
  have hsched : (bytesSchedule P domain n hn ls).profile = P := rfl
  have hdom : (bytesSchedule P domain n hn ls).domain.val = domain := U16.ofNat_val_of_lt hd
  have := sealBytesList_is_sealEpoch (bytesSchedule P domain n hn ls) (fun h => padPrf P (pads h.tick.val) h)
    (cid := pid) hp e (fun t => bytesReceived (bytesSchedule P domain n hn ls) (rs t)) salt
  rw [hdom] at this
  exact this

/-! ## §7. The absent commitment, the opening check, the topic -/

def commitAbsentBytesList (mask salt : List UInt8) : List UInt8 :=
  if mask.all (· ≤ 1) = true ∧ salt.length = 32 then (commitAbsent (openingOf mask salt)).val else []

@[export minidregg_channel_commit_absent]
def commitAbsentBytes (mask salt : ByteArray) : ByteArray :=
  ⟨(commitAbsentBytesList mask.toList salt.toList).toArray⟩

/-- **The commitment export is `commitAbsent`** of the opening the bytes encode. -/
theorem commitAbsentBytesList_is_commitAbsent (o : AbsentOpening) :
    commitAbsentBytesList (o.mask.map bit) o.salt.val = (commitAbsent o).val := by
  have hopen : openingOf (o.mask.map bit) o.salt.val = o := by
    obtain ⟨mask, salt⟩ := o
    simp only [openingOf, map_beq_one_bit]
    congr 1
    exact Blob.ext (fit_val_of_length _ salt.property)
  simp only [commitAbsentBytesList, all_bit_le_one, o.salt.property, and_self, if_true, hopen]

/-- `0` opened; `1 c` refused by `openRecord` with reason code `c` (`0` maskLength, `1` maskByte,
`2` unknownClass, `3` notOpening); `2` the record bytes are not a canonical record. -/
def openingVerdict : Except OpeningRefusal AbsentOpening → List UInt8
  | .ok _ => [0]
  | .error .maskLength => [1, 0]
  | .error .maskByte => [1, 1]
  | .error .unknownClass => [1, 2]
  | .error .notOpening => [1, 3]

def openBytesList (record opening : List UInt8) : List UInt8 :=
  match EpochRecord.decode record with
  | none => [2]
  | some r => openingVerdict (openRecord r opening)

@[export minidregg_channel_open]
def openBytes (record opening : ByteArray) : ByteArray :=
  ⟨(openBytesList record.toList opening.toList).toArray⟩

/-- **The opening export is `openRecord`** on the record the bytes encode. -/
theorem openBytesList_is_openRecord (r : EpochRecord) (opening : List UInt8) :
    openBytesList r.encode opening = openingVerdict (openRecord r opening) := by
  simp [openBytesList, epochRecord_decode_encode]

/-- A witness given the honest seal's record and opening reads `opened`. -/
theorem sealed_opening_opens (sched : Schedule) (prf : FillPrf) {cid : UInt8}
    (hp : profileOfId cid = some sched.profile) (nfits : sched.n < 2 ^ 32) (e : UInt64)
    (rx : Nat → List (Submission sched.profile)) (salt : Digest) :
    openBytesList (sealEpoch sched prf cid e rx salt).encode (epochOpening sched prf e rx salt).encode = [0] := by
  rw [openBytesList_is_openRecord, openRecord_epochOpening sched prf cid e rx salt hp nfits]
  rfl

/-- The refusing pole of the opening export: an opening of the wrong length is refused `maskLength`. -/
theorem openBytesList_wrong_length {r : EpochRecord} {P : Profile} (cls : profileOfId r.classId = some P)
    {bytes : List UInt8} (wrong : bytes.length ≠ P.E * r.n.toNat + 32) :
    openBytesList r.encode bytes = [1, 0] := by
  rw [openBytesList_is_openRecord, openRecord_wrong_length_refused cls wrong]
  rfl

def topicBytesList (domain epoch : Nat) : List UInt8 := channelTopic (U16.ofNat domain) (UInt64.ofNat epoch)

@[export minidregg_channel_topic]
def topicBytes (domain : UInt16) (epoch : UInt64) : ByteArray :=
  ⟨(topicBytesList domain.toNat epoch.toNat).toArray⟩

/-! ## §8. The record's tick roots, for a member's own-slot check (CH-CLIENT-1) -/

/-- `domain 2 | epoch 8 | the E tick roots` of a canonical record, empty otherwise. A member compares
each root with the one it verified on the signed frame and the vector the frame carried (CHANNELS §4
step 6; `own_omission_evident`'s `Included`). -/
def recordRootsBytesList (bytes : List UInt8) : List UInt8 :=
  match EpochRecord.decode bytes with
  | none => []
  | some r => be16 r.domain ++ Minidregg.Pred.HashEqDigest.be 8 r.epoch.toNat ++ r.tickRoots.flatMap Blob.val

@[export minidregg_channel_record_roots]
def recordRootsBytes (record : ByteArray) : ByteArray := ⟨(recordRootsBytesList record.toList).toArray⟩

/-- **The roots export reads the record's own fields** off its canonical encoding. -/
theorem recordRootsBytesList_encode (r : EpochRecord) :
    recordRootsBytesList r.encode =
      be16 r.domain ++ Minidregg.Pred.HashEqDigest.be 8 r.epoch.toNat ++ r.tickRoots.flatMap Blob.val := by
  simp [recordRootsBytesList, epochRecord_decode_encode]

/-- The refusing pole: bytes that are no record's encoding have no roots. -/
theorem recordRootsBytesList_refuses {bytes : List UInt8} (h : EpochRecord.decode bytes = none) :
    recordRootsBytesList bytes = [] := by
  simp [recordRootsBytesList, h]

end Minidregg.Kernel.DomainEpochExport
