/-
# Theory.Channel.Lease — the schedule, its leases, the relay's tick assembly and its fan-out

CHANNELS.md §2.3–§2.4 and §4 (revision 2). A *slot* is a residue class `ρ < n` of a room's schedule; a
*lease* names its holder for a window of channel epochs. Each tick the relay **assembles** one vector
in slot order: at position `ρ` the first received cell that the slot's live lease holder sent under
the position's header, and otherwise a **fill cell** — the same size, the same header, its bytes the
relay's PRF stream for that position — recording the position as absent in the mask it keeps for the
operator and the witnesses. It then **fans out** to every slot, an offline slot's copy going to its
mailbox.

`assemble` and `fanout` are the functions the relay links (`@[export]` at the end): the Rust relay
never re-implements them (§2.3, the census rule).

Two places where this file's statements differ from §2.3's PROPOSED Lean, both reported:
* `Lease.cellsPerTick` is gone. The header (`domain | epoch | tick | slot`, §2.2) has no per-slot cell
  index, so two cells of one slot in one tick are indistinguishable by position; capacity above the
  class rate is therefore *more slots* (§2.3: "bought as extra slots"), and the rate bound is the
  number of slots a subject holds (`leasedSlots`).
* `no_lease_no_cell` needs `c ≠ fillCell …`: the relay itself puts a cell at an unleased position (the
  fill), and it is in the vector. The hypothesis is load-bearing (`fill_at_unleased_slot_assembled`).
-/
import Theory.Channel.Cell

namespace Minidregg.Theory.Channel

set_option autoImplicit false

/-- A subject (holder) identity. -/
abbrev SubjectId := Nat

/-- A channel lease: `holder` holds slot `slot` of the schedule of domain `domain`, at class `profile`,
for channel epochs in `[window.1, window.2)`. -/
structure Lease where
  domain : U16
  holder : SubjectId
  slot : Nat
  profile : Profile
  window : Nat × Nat
  deriving DecidableEq

def Lease.liveAt (l : Lease) (e : Nat) : Bool := decide (l.window.1 ≤ e) && decide (e < l.window.2)

/-- A room's schedule: `n` slots of class `profile` in domain `domain`, and the leases on them. Slots
and ticks ride in the header's two-byte fields, so `n ≤ 2¹⁶` (`Profile.epochFits` does the same for
`E`). -/
structure Schedule where
  domain : U16
  profile : Profile
  n : Nat
  leases : List Lease
  slotsFit : n ≤ 65536

namespace Schedule

variable (sched : Schedule)

/-- The slots, in schedule order. -/
def slots : List Nat := List.range sched.n

/-- The live lease on slot `ρ` at epoch `e`: the first lease on that slot, of this schedule's domain
and class, whose window holds `e`. A lease of another class or domain is never live here. -/
def leaseAt (e ρ : Nat) : Option Lease :=
  sched.leases.find? fun l => l.slot == ρ && l.liveAt e && l.domain == sched.domain && l.profile == sched.profile

def holderOf (e ρ : Nat) : Option SubjectId := (sched.leaseAt e ρ).map (·.holder)

/-- The header of position `(e, t, ρ)`. The header's epoch is `e mod 2¹⁶`. -/
def headerAt (e t ρ : Nat) : Header := ⟨sched.domain, U16.ofNat e, U16.ofNat t, U16.ofNat ρ⟩

/-- How many slots `s` holds at epoch `e`: its cells per tick. -/
def leasedSlots (e : Nat) (s : SubjectId) : Nat := (sched.slots.filter fun ρ => sched.holderOf e ρ == some s).length

theorem mem_slots {ρ : Nat} : ρ ∈ sched.slots ↔ ρ < sched.n := by simp [slots]

theorem headerAt_slot {e t ρ : Nat} (h : ρ < sched.n) : (sched.headerAt e t ρ).slot.val = ρ :=
  U16.ofNat_val_of_lt (Nat.lt_of_lt_of_le h sched.slotsFit)

end Schedule

/-! ## The fill -/

/-- The relay's fill stream: `PRF(fillKey, epoch ‖ tick ‖ slot)` as a byte stream per position. -/
abbrev FillPrf := Header → List UInt8

/-- The fill cell at a position: the position's header and the first `C − 8` bytes of the PRF stream,
parsed in the layout the tick selects (so a fill at tick 0 has the duty layout, with PRF bytes where a
holder's VRF proof would be — which is why a missing duty cell still reaches readers, §2.4). -/
def fillCell (P : Profile) (prf : FillPrf) (h : Header) : Cell P := Cell.ofRaw h (fit P.bodyLen (prf h))

/-- **`fill_is_cell_shaped`** (CHANNELS.md §2.2, revision 2): a fill is exactly `C` bytes and carries
the position's header. -/
theorem fill_is_cell_shaped (P : Profile) (prf : FillPrf) (h : Header) :
    (fillCell P prf h).encode.length = P.C ∧ (fillCell P prf h).header = h :=
  ⟨cell_size_exact _, Cell.ofRaw_header _ _⟩

/-! ## Assembly -/

/-- A received cell with the subject whose access link delivered it (the relay sees slot = holder at
T3, §2.3). -/
abbrev Submission (P : Profile) := SubjectId × Cell P

/-- Where a position's cell came from: the slot's holder, or the relay's fill. -/
inductive Source where
  | fill
  | holder (s : SubjectId)
  deriving DecidableEq, Repr

namespace Schedule

variable (sched : Schedule)

/-- The relay accepts a submission at position `(e, t, ρ)` when its sender holds the live lease on `ρ`
and its header is the position's header. -/
def accepts (e t ρ : Nat) (sub : Submission sched.profile) : Bool :=
  sched.holderOf e ρ == some sub.1 && sub.2.header == sched.headerAt e t ρ

/-- One position of the tick vector: the first accepted submission, else the fill. -/
def assembleAt (prf : FillPrf) (e t : Nat) (received : List (Submission sched.profile)) (ρ : Nat) :
    Cell sched.profile × Source :=
  match received.find? (sched.accepts e t ρ) with
  | some (s, c) => (c, .holder s)
  | none => (fillCell sched.profile prf (sched.headerAt e t ρ), .fill)

/-- The tick vector with each position's source. -/
def assembleTagged (prf : FillPrf) (e t : Nat) (received : List (Submission sched.profile)) :
    List (Cell sched.profile × Source) :=
  sched.slots.map (sched.assembleAt prf e t received)

/-- **`assemble`**: the relay's tick vector, `n` cells in slot order. -/
def assemble (prf : FillPrf) (e t : Nat) (received : List (Submission sched.profile)) : List (Cell sched.profile) :=
  (sched.assembleTagged prf e t received).map Prod.fst

/-- The absent mask of the tick (`true` = filled): kept for the operator and the witnesses, never in the
member-readable channel cell (§2.4). -/
def absentMask (prf : FillPrf) (e t : Nat) (received : List (Submission sched.profile)) : List Bool :=
  (sched.assembleTagged prf e t received).map fun x => x.2 == .fill

theorem assemble_length (prf : FillPrf) (e t : Nat) (received : List (Submission sched.profile)) :
    (sched.assemble prf e t received).length = sched.n := by
  simp [assemble, assembleTagged, slots]

theorem assembleAt_header (prf : FillPrf) (e t : Nat) (received : List (Submission sched.profile)) (ρ : Nat) :
    (sched.assembleAt prf e t received ρ).1.header = sched.headerAt e t ρ := by
  unfold assembleAt
  split
  · rename_i s c hf
    have := List.find?_some hf
    simp only [accepts, Bool.and_eq_true, beq_iff_eq] at this
    exact this.2
  · exact (fill_is_cell_shaped _ _ _).2

/-- What a holder-sourced position holds: a cell its source sent, and the source holds the slot. -/
theorem assembleAt_holder {prf : FillPrf} {e t : Nat} {received : List (Submission sched.profile)} {ρ : Nat}
    {s : SubjectId} (h : (sched.assembleAt prf e t received ρ).2 = .holder s) :
    sched.holderOf e ρ = some s ∧ (s, (sched.assembleAt prf e t received ρ).1) ∈ received := by
  unfold assembleAt at h ⊢
  split at h
  · rename_i s' c hf
    cases h
    have := List.find?_some hf
    simp only [accepts, Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨this.1, List.mem_of_find?_eq_some hf⟩
  · cases h

/-- **`header_is_schedule`** (CHANNELS.md §2.2): every cell of the vector carries the header of its
position. -/
theorem header_is_schedule (prf : FillPrf) (e t : Nat) (received : List (Submission sched.profile))
    {c : Cell sched.profile} (inVector : c ∈ sched.assemble prf e t received) :
    ∃ ρ, ρ < sched.n ∧ c.header = sched.headerAt e t ρ := by
  simp only [assemble, assembleTagged, List.map_map, List.mem_map, Function.comp] at inVector
  obtain ⟨ρ, hρ, rfl⟩ := inVector
  exact ⟨ρ, (sched.mem_slots).1 hρ, sched.assembleAt_header _ _ _ _ _⟩

/-- **`slot_rate_bounded`** (CHANNELS.md §2.3): in any assembled vector, the positions holding a cell
`s` sent number at most the slots `s` holds — whatever `s` submits, and however many times. -/
theorem slot_rate_bounded (prf : FillPrf) (e t : Nat) (received : List (Submission sched.profile)) (s : SubjectId) :
    (sched.assembleTagged prf e t received).countP (fun x => x.2 == .holder s) ≤ sched.leasedSlots e s := by
  unfold assembleTagged leasedSlots
  rw [List.countP_map, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro ρ _ hρ
  simp only [Function.comp, beq_iff_eq] at hρ ⊢
  exact (sched.assembleAt_holder hρ).1

/-- §2.3's own form of the rate statement, counting positions by their header's slot holder: it is an
EQUALITY, not a bound — the vector is constant-shape, so `s`'s slots appear exactly once each whether
`s` sent, sent twice, or was silent (fills carry the slot's header). That is why the rate bound that
says something is `slot_rate_bounded`, which counts by source. -/
theorem slot_positions_exact (prf : FillPrf) (e t : Nat) (received : List (Submission sched.profile)) (s : SubjectId) :
    (sched.assemble prf e t received).countP (fun c => sched.holderOf e c.header.slot.val == some s) =
      sched.leasedSlots e s := by
  unfold assemble assembleTagged leasedSlots
  rw [List.map_map, List.countP_map, ← List.countP_eq_length_filter]
  apply List.countP_congr
  intro ρ hρ
  simp only [Function.comp, sched.assembleAt_header, sched.headerAt_slot ((sched.mem_slots).1 hρ)]

/-- **`no_lease_no_cell`** (CHANNELS.md §2.3): a cell whose slot has no live lease is not in the vector
— unless it is byte-for-byte the relay's own fill for its header. -/
theorem no_lease_no_cell (prf : FillPrf) (e t : Nat) (received : List (Submission sched.profile))
    (c : Cell sched.profile) (noLease : sched.leaseAt e c.header.slot.val = none)
    (notFill : c ≠ fillCell sched.profile prf c.header) : c ∉ sched.assemble prf e t received := by
  intro inVector
  simp only [assemble, assembleTagged, List.map_map, List.mem_map, Function.comp] at inVector
  obtain ⟨ρ, hρ, hc⟩ := inVector
  have hhead : c.header = sched.headerAt e t ρ := hc ▸ sched.assembleAt_header _ _ _ _ _
  have hslot : c.header.slot.val = ρ := by rw [hhead]; exact sched.headerAt_slot ((sched.mem_slots).1 hρ)
  unfold assembleAt at hc
  split at hc
  · rename_i s c' hf
    have := List.find?_some hf
    simp only [accepts, Bool.and_eq_true, beq_iff_eq, holderOf, ← hslot, noLease] at this
    cases this.1
  · exact notFill (by rw [hhead]; exact hc.symm)

/-- The admitting pole of `no_lease_no_cell`: the holder's cell, sent under its position's header and
alone in being accepted there, is exactly what the vector holds at that position. -/
theorem holder_cell_assembled (prf : FillPrf) (e t : Nat) (received : List (Submission sched.profile))
    {ρ : Nat} {s : SubjectId} {c : Cell sched.profile} (hρ : ρ < sched.n)
    (holds : sched.holderOf e ρ = some s) (header : c.header = sched.headerAt e t ρ) (sent : (s, c) ∈ received)
    (alone : ∀ sub ∈ received, sched.accepts e t ρ sub = true → sub = (s, c)) :
    sched.assembleAt prf e t received ρ = (c, .holder s) ∧ c ∈ sched.assemble prf e t received := by
  have acc : sched.accepts e t ρ (s, c) = true := by simp [accepts, holds, header]
  have hfind : received.find? (sched.accepts e t ρ) = some (s, c) := by
    cases hf : received.find? (sched.accepts e t ρ) with
    | none => exact absurd acc (by simpa using List.find?_eq_none.1 hf _ sent)
    | some sub => rw [alone sub (List.mem_of_find?_eq_some hf) (List.find?_some hf)]
  have hat : sched.assembleAt prf e t received ρ = (c, .holder s) := by simp [assembleAt, hfind]
  refine ⟨hat, ?_⟩
  simp only [assemble, assembleTagged, List.map_map, List.mem_map, Function.comp]
  exact ⟨ρ, (sched.mem_slots).2 hρ, by rw [hat]⟩

/-- A subject that does not hold slot `ρ` is never the source of position `ρ`, whatever it sends. -/
theorem nonholder_never_source (prf : FillPrf) (e t : Nat) (received : List (Submission sched.profile))
    {ρ : Nat} {s : SubjectId} (notHolder : sched.holderOf e ρ ≠ some s) :
    (sched.assembleAt prf e t received ρ).2 ≠ .holder s :=
  fun h => notHolder (sched.assembleAt_holder h).1

end Schedule

/-! ## Fan-out -/

/-- Where a slot's copy of the tick vector goes. -/
inductive Route where
  | live
  | mailbox
  deriving DecidableEq, Repr

/-- Whether each slot's holder is connected at this tick. -/
abbrev Presence := Nat → Bool

/-- **`fanout`** (§2.4, §4): every slot, every tick, in slot order; an offline slot's copy goes to its
mailbox. -/
def fanout (sched : Schedule) (p : Presence) : List (Nat × Route) :=
  sched.slots.map fun ρ => (ρ, if p ρ then .live else .mailbox)

/-- **`fanout_independent_of_presence`** (CHANNELS.md §2.4, revision 2). -/
theorem fanout_independent_of_presence (sched : Schedule) (p : Presence) :
    (fanout sched p).map Prod.fst = sched.slots := by
  simp [fanout, Function.comp_def]

/-- The refuted alternative: fan out only to connected slots (the simulator's draft relay). -/
def fanoutConnected (sched : Schedule) (p : Presence) : List (Nat × Route) :=
  (sched.slots.filter p).map fun ρ => (ρ, .live)

/-! ## Teeth on a concrete schedule -/

namespace Example

/-- Domain 7 at P1, three slots: slot 0 leased to subject 10, slot 1 to subject 11, slot 2 unleased;
plus a P2 lease on slot 2, which is not of this schedule's class and so never live. -/
def sched : Schedule :=
  { domain := ⟨7, by decide⟩, profile := P1, n := 3,
    leases := [⟨⟨7, by decide⟩, 10, 0, P1, (0, 5)⟩, ⟨⟨7, by decide⟩, 11, 1, P1, (0, 5)⟩,
      ⟨⟨7, by decide⟩, 12, 2, P2, (0, 5)⟩],
    slotsFit := by decide }

def prf : FillPrf := fun _ => []

/-- A regular cell of `sched` at epoch 1, tick 3, slot `ρ`, its sealed bytes all `b`. -/
def cellAt (ρ : Nat) (b : UInt8) : Cell P1 :=
  Cell.ofRaw (sched.headerAt 1 3 ρ) (fit P1.bodyLen (List.replicate 248 b))

/-- Subject 11 (holder of slot 1) also sends a cell under slot 0's header; subject 10 is silent. -/
def received : List (Submission sched.profile) := [(11, cellAt 0 0xEE), (11, cellAt 1 0x11)]

theorem class_mismatch_not_live : sched.leaseAt 1 2 = none := by decide +kernel

theorem example_sources :
    (sched.assembleTagged prf 1 3 received).map Prod.snd = [.fill, .holder 11, .fill] := by decide +kernel

theorem example_mask : sched.absentMask prf 1 3 received = [true, false, true] := by decide +kernel

/-- The holder filter is load-bearing: an assembly that accepts by header alone puts subject 11's cell
in subject 10's position. -/
def assembleByHeaderOnly (e t : Nat) (rcv : List (Submission sched.profile)) : List (Cell sched.profile) :=
  sched.slots.map fun ρ =>
    match rcv.find? (fun sub => sub.2.header == sched.headerAt e t ρ) with
    | some (_, c) => c
    | none => fillCell sched.profile prf (sched.headerAt e t ρ)

theorem header_only_admits_nonholder : cellAt 0 0xEE ∈ assembleByHeaderOnly 1 3 received := by decide +kernel
theorem holder_filter_refuses_nonholder : cellAt 0 0xEE ∉ sched.assemble prf 1 3 received := by decide +kernel

/-- `no_lease_no_cell`'s `notFill` is load-bearing: the relay's own fill sits at the unleased slot 2. -/
theorem fill_at_unleased_slot_assembled :
    sched.leaseAt 1 2 = none ∧ fillCell sched.profile prf (sched.headerAt 1 3 2) ∈ sched.assemble prf 1 3 received := by
  decide +kernel

/-- `slot_rate_bounded` is attained (subject 11 holds one slot and fills it) and binds the sender of a
second cell (subject 11 sent two; one is assembled). -/
theorem rate_attained :
    (sched.assembleTagged prf 1 3 received).countP (fun x => x.2 == .holder 11) = 1 ∧ sched.leasedSlots 1 11 = 1 ∧
      (received.filter (·.1 == 11)).length = 2 := by decide +kernel

/-- Connected-only fan-out depends on presence: with slot 0 offline the copies go to slots 1, 2 only. -/
theorem fanoutConnected_depends_on_presence :
    (fanoutConnected sched (fun _ => true)).map Prod.fst = [0, 1, 2] ∧
      (fanoutConnected sched (fun ρ => ρ != 0)).map Prod.fst = [1, 2] := by decide

/-- The design's fan-out at the same two presences: the same slot order; only the route differs. -/
theorem fanout_same_order :
    fanout sched (fun _ => true) = [(0, .live), (1, .live), (2, .live)] ∧
      fanout sched (fun ρ => ρ != 0) = [(0, .mailbox), (1, .live), (2, .live)] := by decide

end Example

/-! ## Byte entry points (`@[export]`) -/

/-- `k` big-endian bytes of `v` (mod `2^(8k)`). -/
def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, v => beBytes k (v / 256) ++ [(v % 256).toUInt8]

def readBE (bytes : List UInt8) : Nat := bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Split into `w`-byte records; `none` unless the length is a multiple of `w`. -/
def records (w : Nat) (bytes : List UInt8) : Option (List (List UInt8)) :=
  if w = 0 then none else
  if bytes.length % w = 0 then some ((List.range (bytes.length / w)).map fun i => (bytes.drop (i * w)).take w)
  else none

/-- Lease records, 28 bytes each: `holder 8 | slot 4 | from 8 | to 8`. -/
def parseLease (domain : U16) (P : Profile) (r : List UInt8) : Lease :=
  ⟨domain, readBE (r.take 8), readBE ((r.drop 8).take 4), P, (readBE ((r.drop 12).take 8), readBE (r.drop 20))⟩

/-- The relay's tick assembly on bytes. Inputs: the class id (`profileOfId`), the domain, `n`, the
channel epoch, the tick, the lease records, the received records (`sender 8 | cell C`), and the fill
PRF stream for the whole tick (`n × (C − 8)` bytes, position-major; a short stream is zero-extended).
Output: the `n` cells (`n × C` bytes) then the absent mask (`n` bytes, `1` = filled). The empty list
refuses: an unknown class, `n > 2¹⁶`, or a record stream that does not divide. -/
def assembleBytesList (pid : UInt8) (domain : Nat) (n epoch tick : Nat) (leaseBytes receivedBytes pad : List UInt8) :
    List UInt8 :=
  match profileOfId pid with
  | none => []
  | some P =>
    if hn : n ≤ 65536 then
      match records 28 leaseBytes, records (8 + P.C) receivedBytes with
      | some ls, some rs =>
        let dom := U16.ofNat domain
        let sched : Schedule := ⟨dom, P, n, ls.map (parseLease dom P), hn⟩
        let received : List (Submission sched.profile) :=
          rs.filterMap fun r => (Cell.decode sched.profile (r.drop 8)).map fun c => (readBE (r.take 8), c)
        let prf : FillPrf := fun h => (pad.drop (h.slot.val * P.bodyLen)).take P.bodyLen
        let tagged := sched.assembleTagged prf epoch tick received
        tagged.flatMap (fun x => x.1.encode) ++ tagged.map fun x => if x.2 == .fill then 1 else 0
      | _, _ => []
    else []

@[export minidregg_channel_assemble]
def assembleBytes (pid : UInt8) (domain : UInt16) (n : UInt32) (epoch : UInt64) (tick : UInt32)
    (leases received pad : ByteArray) : ByteArray :=
  ⟨(assembleBytesList pid domain.toNat n.toNat epoch.toNat tick.toNat leases.toList received.toList pad.toList).toArray⟩

/-- The fan-out on bytes: one presence byte per slot in (non-zero = connected); out, per slot in send
order, `slot 4 | route 1` (`0` live, `1` mailbox). Empty when `n > 2¹⁶` or the class is unknown. -/
def fanoutBytesList (pid : UInt8) (n : Nat) (presence : List UInt8) : List UInt8 :=
  match profileOfId pid with
  | none => []
  | some P =>
    if hn : n ≤ 65536 then
      let sched : Schedule := ⟨U16.ofNat 0, P, n, [], hn⟩
      (fanout sched (fun ρ => presence.getD ρ 0 != 0)).flatMap fun x =>
        beBytes 4 x.1 ++ [if x.2 == .live then 0 else 1]
    else []

@[export minidregg_channel_fanout]
def fanoutBytes (pid : UInt8) (n : UInt32) (presence : ByteArray) : ByteArray :=
  ⟨(fanoutBytesList pid n.toNat presence.toList).toArray⟩

theorem sum_map_const {α : Type} (l : List α) (c : Nat) : (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.succ_mul, Nat.add_comm]

/-- The byte fan-out's length is `5 n` at every presence: its shape carries no presence. -/
theorem fanoutBytesList_length {pid : UInt8} {P : Profile} (hp : profileOfId pid = some P) {n : Nat}
    (hn : n ≤ 65536) (presence : List UInt8) : (fanoutBytesList pid n presence).length = 5 * n := by
  have hb : ∀ k v, (beBytes k v).length = k := by
    intro k; induction k with
    | zero => intro v; rfl
    | succ k ih => intro v; simp [beBytes, ih]
  simp only [fanoutBytesList, hp, hn, ↓reduceDIte, List.length_flatMap, List.length_append, hb,
    List.length_singleton]
  simp [fanout, Schedule.slots, Function.comp_def, sum_map_const, Nat.mul_comm]

/-- The byte assembly's length is `n (C + 1)` whenever it does not refuse. -/
theorem assembleBytesList_length {pid : UInt8} {P : Profile} (hp : profileOfId pid = some P) {domain n epoch tick : Nat}
    {leaseBytes receivedBytes pad : List UInt8} (hn : n ≤ 65536)
    (hl : (records 28 leaseBytes).isSome) (hr : (records (8 + P.C) receivedBytes).isSome) :
    (assembleBytesList pid domain n epoch tick leaseBytes receivedBytes pad).length = n * (P.C + 1) := by
  obtain ⟨ls, hls⟩ := Option.isSome_iff_exists.1 hl
  obtain ⟨rs, hrs⟩ := Option.isSome_iff_exists.1 hr
  simp only [assembleBytesList, hp, hn, ↓reduceDIte, hls, hrs, List.length_append, List.length_flatMap,
    List.length_map, cell_size_exact]
  simp [Schedule.assembleTagged, Schedule.slots, Function.comp_def, sum_map_const, Nat.mul_add]

namespace Example

/-- Smoke on bytes: `sched`'s two leases, one received cell (subject 11 on slot 1), a 3-slot P1 tick:
`3 × 256` cell bytes and the mask `[1, 0, 1]`. -/
def leaseRecords : List UInt8 :=
  beBytes 8 10 ++ beBytes 4 0 ++ beBytes 8 0 ++ beBytes 8 5 ++ beBytes 8 11 ++ beBytes 4 1 ++ beBytes 8 0 ++ beBytes 8 5

def receivedRecords : List UInt8 := beBytes 8 11 ++ (cellAt 1 0x11).encode

theorem assembleBytes_smoke :
    (assembleBytesList 1 7 3 1 3 leaseRecords receivedRecords []).length = 3 * 257 ∧
    (assembleBytesList 1 7 3 1 3 leaseRecords receivedRecords []).drop 768 = [1, 0, 1] ∧
    ((assembleBytesList 1 7 3 1 3 leaseRecords receivedRecords []).drop 256).take 256 = (cellAt 1 0x11).encode := by
  decide +kernel

theorem fanoutBytes_smoke :
    fanoutBytesList 1 3 [1, 0, 1] = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 2, 0] := by decide

end Example


end Minidregg.Theory.Channel
