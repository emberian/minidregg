/-
# Theory.Channel.Trace — the observers and the trace theorems

CHANNELS.md §2.4 "The observable trace" (revision 2). A run of a channel is deterministic: at global
tick `k` (epoch `k / E`, tick `k mod E`) every connected holder emits one cell — payload or padding,
sealed — at the offset its emission rule gives; the relay assembles the tick vector (`assemble`, with
fills) and fans it out (`fanout`). Each observer sees a projection of the run:

* the **wire** — every access link: who emitted, when, and the cell (as a non-recipient sees it); the
  fan-out routes; the delivered vector;
* the **relay** — per slot, what arrived from whom and when; the vector with each position's source;
* the **operator** — the relay's view and the absent mask (at n = 1 node the operator IS the relay);
* a **witness** — the vector and the absent mask (§4: at T3 witnesses get the relay's tick vector and
  the mask opening);
* a **member** that is not a recipient — the vector delivered to it, when its copy arrives (its
  position in the send order), and the absent mask only if the relay publishes it to members.

"As a non-recipient sees it" is the one cryptographic seam, and it is a HYPOTHESIS here, never a
theorem: a cell's sealed body is reduced to `Sealing.observe`, and

* `PayloadHidden S` — what a non-recipient observes of a holder's sealed body does not depend on the
  payload (real or padding) — stands for §2.2's named reduction `cover_indistinguishable`
  (`Adv^{ANO-CCA}_{KEM}(q_K) + N_cells·Adv^{IND-CPA+INT}_{AEAD} + Adv^{PRF}_{viewtag}`), stated, as a
  deterministic kernel must, as an equality of the observer's projection;
* `FillHidden S prf` — at a regular (non-duty) position the relay's fill body observes the same as the
  holder's sealed body — stands for "a PRF stream is indistinguishable from an AEAD ciphertext".

Both are satisfiable (`Example.toy_payloadHidden`, `Example.toy_fillHidden`, on a sealing whose
observation is NOT constant) and both are load-bearing (`Example.leaky_breaks_membership_theorem`,
`Example.fill_distinguishable_at_duty_tick`).
-/
import Theory.Channel.Lease

namespace Minidregg.Theory.Channel

set_option autoImplicit false

/-! ## The sealing seam and the emission rule -/

/-- A sealing model at class `P`: the body a holder emits under a header for a payload (`none` =
padding), and what a non-recipient observes of a body. -/
structure Sealing (P : Profile) (Msg Obs : Type) where
  sealBody : SubjectId → Header → Option Msg → Blob P.bodyLen
  observe : Header → Blob P.bodyLen → Obs

/-- **The sealing hypothesis, payload half.** A non-recipient's observation of a holder's sealed body is
independent of the payload, padding included. -/
def PayloadHidden {P : Profile} {Msg Obs : Type} (S : Sealing P Msg Obs) : Prop :=
  ∀ (s : SubjectId) (h : Header) (m₁ m₂ : Option Msg), S.observe h (S.sealBody s h m₁) = S.observe h (S.sealBody s h m₂)

/-- **The sealing hypothesis, fill half.** At a regular position, the relay's fill body observes as the
holder's sealed body does. Not asked at duty positions: the relay cannot forge a VRF proof (§2.4). -/
def FillHidden {P : Profile} {Msg Obs : Type} (S : Sealing P Msg Obs) (prf : FillPrf) : Prop :=
  ∀ (s : SubjectId) (h : Header) (m : Option Msg),
    isDutyTick h = false → S.observe h (fit P.bodyLen (prf h)) = S.observe h (S.sealBody s h m)

/-- A client's emission rule: the offset (ms after the frame) at which it emits a cell carrying this
payload, or `none` for silence. -/
abbrev Emission (Msg : Type) := Option Msg → Option Nat

/-- Emit every tick, at one offset, whatever the payload (§2.1: at `frame + T_tick − δ`). -/
def ConstantEmission {Msg : Type} (em : Emission Msg) : Prop := ∃ off, ∀ m, em m = some off

/-- The design's rule at a class: every tick at `T_tick − δ`. -/
def designEmission (P : Profile) (Msg : Type) : Emission Msg := fun _ => some (P.tickMs - P.deltaMs)

theorem designEmission_constant (P : Profile) (Msg : Type) : ConstantEmission (designEmission P Msg) :=
  ⟨_, fun _ => rfl⟩

/-! ## The relay's policy -/

/-- `fills`: absent positions get fill cells (else they are delivered as absent). `maskToMembers`: the
absent mask is published in the member-readable channel cell. `constantFanout`: every slot every tick
(else only connected slots). -/
structure RelayPolicy where
  fills : Bool
  maskToMembers : Bool
  constantFanout : Bool
  deriving DecidableEq, Repr

/-- §2.4's default: fill absent positions, keep the mask from members. -/
def RelayFills (pol : RelayPolicy) : Prop := pol.fills = true ∧ pol.maskToMembers = false

def ConstantFanout (pol : RelayPolicy) : Prop := pol.constantFanout = true

/-- The policy §2.4 and §4 write down. -/
def designPolicy : RelayPolicy := ⟨true, false, true⟩

theorem designPolicy_fills : RelayFills designPolicy := ⟨rfl, rfl⟩
theorem designPolicy_constantFanout : ConstantFanout designPolicy := rfl

/-! ## A run -/

/-- Per global tick and slot, the payload the slot's holder has for that cell (`none` = padding). -/
abbrev Traffic (Msg : Type) := Nat → Nat → Option Msg

/-- Per global tick, which slots' holders are connected. -/
abbrev Presences := Nat → Presence

/-- A channel domain (§2.4): the schedule (the membership), the sealing model, the relay's fill PRF, and
the clients' emission rule. -/
structure Domain (Msg Obs : Type) where
  sched : Schedule
  S : Sealing sched.profile Msg Obs
  prf : FillPrf
  em : Emission Msg

/-- What a non-recipient sees of one cell: its header, its byte length, and the observation of its
body. -/
structure CellObs (Obs : Type) where
  header : Header
  len : Nat
  body : Obs
  deriving DecidableEq, Repr

namespace Domain

variable {Msg Obs : Type} (X : Domain Msg Obs)

def epochOf (k : Nat) : Nat := k / X.sched.profile.E
def tickOf (k : Nat) : Nat := k % X.sched.profile.E
def hdr (k ρ : Nat) : Header := X.sched.headerAt (X.epochOf k) (X.tickOf k) ρ

/-- The cell slot `ρ`'s holder emits at global tick `k`, with its subject and offset — if the slot is
leased, the holder connected, and its emission rule emits. -/
def emitted (τ : Traffic Msg) (p : Presences) (k ρ : Nat) : Option (SubjectId × Nat × Cell X.sched.profile) :=
  match X.sched.holderOf (X.epochOf k) ρ with
  | none => none
  | some s =>
    if p k ρ then (X.em (τ k ρ)).map fun off => (s, off, Cell.ofRaw (X.hdr k ρ) (X.S.sealBody s (X.hdr k ρ) (τ k ρ)))
    else none

/-- What reaches the relay by the deadline. -/
def received (τ : Traffic Msg) (p : Presences) (k : Nat) : List (Submission X.sched.profile) :=
  X.sched.slots.filterMap fun ρ => (X.emitted τ p k ρ).map fun x => (x.1, x.2.2)

/-- The tick vector with sources: `assemble`, run on what arrived. -/
def tagged (τ : Traffic Msg) (p : Presences) (k : Nat) : List (Cell X.sched.profile × Source) :=
  X.sched.assembleTagged X.prf (X.epochOf k) (X.tickOf k) (X.received τ p k)

def cellObs (c : Cell X.sched.profile) : CellObs Obs := ⟨c.header, c.encode.length, X.S.observe c.header c.bodyBlob⟩

def mask (τ : Traffic Msg) (p : Presences) (k : Nat) : List Bool := (X.tagged τ p k).map fun x => x.2 == .fill

/-- The vector as delivered: a filled position shows as a cell when the relay fills, and as absent
otherwise. -/
def delivered (pol : RelayPolicy) (τ : Traffic Msg) (p : Presences) (k : Nat) : List (Option (CellObs Obs)) :=
  (X.tagged τ p k).map fun x => if pol.fills || x.2 != .fill then some (X.cellObs x.1) else none

def routes (pol : RelayPolicy) (p : Presences) (k : Nat) : List (Nat × Route) :=
  if pol.constantFanout then fanout X.sched (p k) else fanoutConnected X.sched (p k)

/-! ### The observers -/

structure WireTick (Obs : Type) where
  up : List (Nat × SubjectId × Nat × CellObs Obs)
  down : List (Nat × Route)
  vector : List (Option (CellObs Obs))
  deriving DecidableEq

structure RelayTick (Obs : Type) where
  arrivals : List (Nat × Option (SubjectId × Nat × CellObs Obs))
  vector : List (CellObs Obs × Source)
  deriving DecidableEq

structure MemberTick (Obs : Type) where
  /-- the position of the member's copy in the relay's send order: its receipt time -/
  receiptIndex : Nat
  vector : List (Option (CellObs Obs))
  mask : Option (List Bool)
  deriving DecidableEq

def emittedObs (τ : Traffic Msg) (p : Presences) (k ρ : Nat) : Option (SubjectId × Nat × CellObs Obs) :=
  (X.emitted τ p k ρ).map fun x => (x.1, x.2.1, X.cellObs x.2.2)

def wireTick (pol : RelayPolicy) (τ : Traffic Msg) (p : Presences) (k : Nat) : WireTick Obs :=
  { up := X.sched.slots.filterMap fun ρ => (X.emittedObs τ p k ρ).map fun x => (ρ, x)
    down := X.routes pol p k
    vector := X.delivered pol τ p k }

def relayTick (τ : Traffic Msg) (p : Presences) (k : Nat) : RelayTick Obs :=
  { arrivals := X.sched.slots.map fun ρ => (ρ, X.emittedObs τ p k ρ)
    vector := (X.tagged τ p k).map fun x => (X.cellObs x.1, x.2) }

def operatorTick (τ : Traffic Msg) (p : Presences) (k : Nat) : RelayTick Obs × List Bool :=
  (X.relayTick τ p k, X.mask τ p k)

def witnessTick (τ : Traffic Msg) (p : Presences) (k : Nat) : List (CellObs Obs) × List Bool :=
  ((X.tagged τ p k).map fun x => X.cellObs x.1, X.mask τ p k)

def memberTick (pol : RelayPolicy) (τ : Traffic Msg) (p : Presences) (me : Nat) (k : Nat) : MemberTick Obs :=
  { receiptIndex := ((X.routes pol p k).map Prod.fst).idxOf me
    vector := X.delivered pol τ p k
    mask := if pol.maskToMembers then some (X.mask τ p k) else none }

/-- A trace: an observer's view at ticks `0 … ticks − 1`. -/
def trace {α : Type} (view : Nat → α) (ticks : Nat) : List α := (List.range ticks).map view

/-! ### The vector a run assembles -/

theorem emitted_header {τ : Traffic Msg} {p : Presences} {k ρ : Nat} {x : SubjectId × Nat × Cell X.sched.profile}
    (h : X.emitted τ p k ρ = some x) : x.2.2.header = X.hdr k ρ ∧ X.sched.holderOf (X.epochOf k) ρ = some x.1 := by
  unfold emitted at h
  split at h
  · cases h
  · rename_i s hs
    split at h
    · obtain ⟨off, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact ⟨Cell.ofRaw_header _ _, hs⟩
    · cases h

/-- Position `ρ` of the run's vector is the holder's emitted cell when there is one, else the fill:
the uniqueness that makes the relay's `find?` pick the right submission (headers name their slot). -/
theorem assembleAt_run (τ : Traffic Msg) (p : Presences) (k : Nat) {ρ : Nat} (hρ : ρ < X.sched.n) :
    X.sched.assembleAt X.prf (X.epochOf k) (X.tickOf k) (X.received τ p k) ρ =
      match X.emitted τ p k ρ with
      | some x => (x.2.2, .holder x.1)
      | none => (fillCell X.sched.profile X.prf (X.hdr k ρ), .fill) := by
  -- Only slot ρ's own emission is accepted at position ρ.
  have only : ∀ ρ' ∈ X.sched.slots,
      ((X.emitted τ p k ρ').map fun x => (x.1, x.2.2)).any (X.sched.accepts (X.epochOf k) (X.tickOf k) ρ) = true →
        ρ' = ρ := by
    intro ρ' hρ' hacc
    cases he : X.emitted τ p k ρ' with
    | none => simp [he] at hacc
    | some x =>
      simp only [he, Option.map_some, Option.any_some, Schedule.accepts, Bool.and_eq_true, beq_iff_eq] at hacc
      have h1 := (X.emitted_header he).1
      have h2 : (X.hdr k ρ').slot.val = (X.hdr k ρ).slot.val := by rw [← h1, hacc.2]; rfl
      simpa [hdr, X.sched.headerAt_slot ((X.sched.mem_slots).1 hρ'), X.sched.headerAt_slot hρ] using h2
  have self : ∀ x, X.emitted τ p k ρ = some x →
      X.sched.accepts (X.epochOf k) (X.tickOf k) ρ (x.1, x.2.2) = true := by
    intro x hx
    obtain ⟨h1, h2⟩ := X.emitted_header hx
    simp [Schedule.accepts, h2, h1, hdr]
  unfold Schedule.assembleAt received
  rw [List.find?_filterMap]
  cases hf : X.sched.slots.find? (fun a => ((X.emitted τ p k a).map fun x => (x.1, x.2.2)).any
      (X.sched.accepts (X.epochOf k) (X.tickOf k) ρ)) with
  | none =>
    have hnone := List.find?_eq_none.1 hf ρ ((X.sched.mem_slots).2 hρ)
    cases he : X.emitted τ p k ρ with
    | none => simp [hdr]
    | some x => exact absurd (by simpa [he] using self x he) hnone
  | some ρ' =>
    have hp := List.find?_some hf
    have hρ'eq := only ρ' (List.mem_of_find?_eq_some hf) hp
    subst hρ'eq
    have hany := List.find?_some hf
    cases he : X.emitted τ p k ρ' with
    | none => simp [he] at hany
    | some x => simp [he]

/-- The observation of a cell built from a body under a header: that header, `C` bytes, the body's
observation. -/
theorem cellObs_ofRaw (h : Header) (b : Blob X.sched.profile.bodyLen) :
    X.cellObs (Cell.ofRaw h b) = ⟨h, X.sched.profile.C, X.S.observe h b⟩ := by
  simp [cellObs, Cell.ofRaw_header, cell_size_exact, Cell.bodyBlob_ofRaw]

/-- A position's observation, read off the emission. -/
theorem posObs_run (τ : Traffic Msg) (p : Presences) (k : Nat) {ρ : Nat} (hρ : ρ < X.sched.n) :
    (fun x => (X.cellObs x.1, x.2)) (X.sched.assembleAt X.prf (X.epochOf k) (X.tickOf k) (X.received τ p k) ρ) =
      match X.emittedObs τ p k ρ with
      | some x => (x.2.2, .holder x.1)
      | none => (⟨X.hdr k ρ, X.sched.profile.C, X.S.observe (X.hdr k ρ) (fit _ (X.prf (X.hdr k ρ)))⟩, .fill) := by
  rw [X.assembleAt_run τ p k hρ]
  unfold emittedObs
  cases X.emitted τ p k ρ with
  | none => simp only [Option.map_none]; rw [fillCell, X.cellObs_ofRaw]
  | some x => rfl

theorem tagged_eq_map (τ : Traffic Msg) (p : Presences) (k : Nat) :
    X.tagged τ p k =
      X.sched.slots.map (X.sched.assembleAt X.prf (X.epochOf k) (X.tickOf k) (X.received τ p k)) := rfl

/-! ## `observable_trace_depends_only_on_membership` -/

/-- Under constant emission and the payload half of the sealing hypothesis, what every non-recipient
observes of a holder's emission does not depend on the traffic. -/
theorem emittedObs_traffic_invariant (hide : PayloadHidden X.S) (on : ConstantEmission X.em)
    (τ₁ τ₂ : Traffic Msg) (p : Presences) (k ρ : Nat) : X.emittedObs τ₁ p k ρ = X.emittedObs τ₂ p k ρ := by
  obtain ⟨off, hoff⟩ := on
  unfold emittedObs emitted
  cases X.sched.holderOf (X.epochOf k) ρ with
  | none => rfl
  | some s =>
    by_cases hp : p k ρ = true
    · simp only [hp, ↓reduceIte, hoff, Option.map_some, X.cellObs_ofRaw, hide s (X.hdr k ρ) (τ₁ k ρ) (τ₂ k ρ)]
    · simp [hp]

theorem posObs_traffic_invariant (hide : PayloadHidden X.S) (on : ConstantEmission X.em)
    (τ₁ τ₂ : Traffic Msg) (p : Presences) (k : Nat) {ρ : Nat} (hρ : ρ < X.sched.n) :
    (fun x => (X.cellObs x.1, x.2)) (X.sched.assembleAt X.prf (X.epochOf k) (X.tickOf k) (X.received τ₁ p k) ρ) =
      (fun x => (X.cellObs x.1, x.2)) (X.sched.assembleAt X.prf (X.epochOf k) (X.tickOf k) (X.received τ₂ p k) ρ) := by
  rw [X.posObs_run τ₁ p k hρ, X.posObs_run τ₂ p k hρ, X.emittedObs_traffic_invariant hide on τ₁ τ₂ p k ρ]

/-- Every list a view builds from the vector agrees across the two traffics. -/
theorem vector_traffic_invariant {β : Type} (F : CellObs Obs × Source → β) (hide : PayloadHidden X.S)
    (on : ConstantEmission X.em) (τ₁ τ₂ : Traffic Msg) (p : Presences) (k : Nat) :
    (X.tagged τ₁ p k).map (fun x => F (X.cellObs x.1, x.2)) = (X.tagged τ₂ p k).map (fun x => F (X.cellObs x.1, x.2)) := by
  rw [X.tagged_eq_map, X.tagged_eq_map, List.map_map, List.map_map]
  apply List.map_congr_left
  intro ρ hρ
  have := X.posObs_traffic_invariant hide on τ₁ τ₂ p k ((X.sched.mem_slots).1 hρ)
  simp only [Function.comp] at this ⊢
  rw [this]

/-- **`observable_trace_depends_only_on_membership`** (CHANNELS.md §2.4). Fix the membership (the
schedule) and the presence. Under constant emission and `PayloadHidden`, ANY two traffic patterns give
the wire, the relay, the operator, every witness and every non-recipient member equal traces, under
any relay policy. -/
theorem observable_trace_depends_only_on_membership (hide : PayloadHidden X.S) (on : ConstantEmission X.em)
    (pol : RelayPolicy) (τ₁ τ₂ : Traffic Msg) (p : Presences) (me ticks : Nat) :
    trace (X.wireTick pol τ₁ p) ticks = trace (X.wireTick pol τ₂ p) ticks ∧
    trace (X.relayTick τ₁ p) ticks = trace (X.relayTick τ₂ p) ticks ∧
    trace (X.operatorTick τ₁ p) ticks = trace (X.operatorTick τ₂ p) ticks ∧
    trace (X.witnessTick τ₁ p) ticks = trace (X.witnessTick τ₂ p) ticks ∧
    trace (X.memberTick pol τ₁ p me) ticks = trace (X.memberTick pol τ₂ p me) ticks := by
  have up : ∀ k, (X.sched.slots.filterMap fun ρ => (X.emittedObs τ₁ p k ρ).map fun x => (ρ, x)) =
      (X.sched.slots.filterMap fun ρ => (X.emittedObs τ₂ p k ρ).map fun x => (ρ, x)) := by
    intro k; simp only [X.emittedObs_traffic_invariant hide on τ₁ τ₂ p k]
  have arr : ∀ k, (X.sched.slots.map fun ρ => (ρ, X.emittedObs τ₁ p k ρ)) =
      (X.sched.slots.map fun ρ => (ρ, X.emittedObs τ₂ p k ρ)) := by
    intro k; simp only [X.emittedObs_traffic_invariant hide on τ₁ τ₂ p k]
  have vec := fun {β : Type} (F : CellObs Obs × Source → β) => X.vector_traffic_invariant F hide on τ₁ τ₂ p
  have del : ∀ k, X.delivered pol τ₁ p k = X.delivered pol τ₂ p k := fun k =>
    vec (fun y => if pol.fills || y.2 != .fill then some y.1 else none) k
  have msk : ∀ k, X.mask τ₁ p k = X.mask τ₂ p k := fun k => vec (fun y => y.2 == .fill) k
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> apply List.map_congr_left <;> intro k _
  · simp only [wireTick, up k, del k]
  · simp only [relayTick, arr k]; rw [vec (fun y => y) k]
  · simp only [operatorTick, relayTick, arr k, msk k]; rw [vec (fun y => y) k]
  · simp only [witnessTick, msk k]; rw [vec (fun y => y.1) k]
  · simp only [memberTick, del k, msk k]

/-! ### The membership pole, in general -/

/-- Under constant emission, a connected slot's emission is visible exactly when it is leased, and
its subject is the slot's holder. -/
theorem emittedObs_holder (on : ConstantEmission X.em) (τ : Traffic Msg) (p : Presences) (k ρ : Nat)
    (connected : p k ρ = true) : (X.emittedObs τ p k ρ).map (·.1) = X.sched.holderOf (X.epochOf k) ρ := by
  obtain ⟨off, hoff⟩ := on
  unfold emittedObs emitted
  cases X.sched.holderOf (X.epochOf k) ρ with
  | none => rfl
  | some s => simp [connected, hoff]

theorem mem_up {pol : RelayPolicy} {τ : Traffic Msg} {p : Presences} {k ρ : Nat} {x : SubjectId × Nat × CellObs Obs} :
    (ρ, x) ∈ (X.wireTick pol τ p k).up ↔ ρ ∈ X.sched.slots ∧ X.emittedObs τ p k ρ = some x := by
  simp only [wireTick, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨ρ', hρ', x', hx', rfl, rfl⟩; exact ⟨hρ', hx'⟩
  · rintro ⟨hρ, hx⟩; exact ⟨ρ, hρ, x, hx, rfl, rfl⟩

/-- **The membership pole, in general.** Two channels of the same width, at the same epoch, with every
slot connected and both emitting at a constant offset: if the wire's uplink views at one tick agree,
then the two schedules have the same holder on every slot (each at its own epoch for that tick). So the wire reads the membership (and, by
the same uplink, presence) — the leak §2.4 states and the class design accepts. -/
theorem wire_reveals_membership (Y : Domain Msg Obs) (onX : ConstantEmission X.em) (onY : ConstantEmission Y.em)
    (polX polY : RelayPolicy) (τ τ' : Traffic Msg) (p : Presences) (k : Nat) (connected : ∀ ρ, p k ρ = true)
    (width : X.sched.n = Y.sched.n)
    (sameUp : (X.wireTick polX τ p k).up = (Y.wireTick polY τ' p k).up) :
    ∀ ρ, ρ < X.sched.n → X.sched.holderOf (X.epochOf k) ρ = Y.sched.holderOf (Y.epochOf k) ρ := by
  intro ρ hρ
  have hρY : ρ ∈ Y.sched.slots := (Y.sched.mem_slots).2 (width ▸ hρ)
  have hρX : ρ ∈ X.sched.slots := (X.sched.mem_slots).2 hρ
  rw [← X.emittedObs_holder onX τ p k ρ (connected ρ), ← Y.emittedObs_holder onY τ' p k ρ (connected ρ)]
  cases hx : X.emittedObs τ p k ρ with
  | some x =>
    have := (Y.mem_up (pol := polY)).1 (sameUp ▸ (X.mem_up (pol := polX)).2 ⟨hρX, hx⟩)
    rw [this.2]
  | none =>
    cases hy : Y.emittedObs τ' p k ρ with
    | none => rfl
    | some y =>
      have := (X.mem_up (pol := polX)).1 (sameUp.symm ▸ (Y.mem_up (pol := polY)).2 ⟨hρY, hy⟩)
      rw [hx] at this; cases this.2

/-! ## `member_view_independent_of_presence` -/

/-- Presence agrees wherever a duty cell is due (tick 0 of every epoch): the relay cannot forge a VRF
proof, so a missing duty cell is visible to readers (§2.4). Replaces §2.4's `DutiesOnlyWhenPresent`. -/
def PresenceAgreesAtDutyTicks (p₁ p₂ : Presences) : Prop :=
  ∀ k ρ, X.tickOf k = 0 → p₁ k ρ = p₂ k ρ

theorem hdr_isDutyTick (k ρ : Nat) : isDutyTick (X.hdr k ρ) = (X.tickOf k == 0) := by
  have hE := X.sched.profile.epochFits
  have hlt : X.tickOf k < 65536 := Nat.lt_of_lt_of_le (Nat.mod_lt _ hE.1) hE.2
  simp [isDutyTick, hdr, Schedule.headerAt, U16.ofNat_val_of_lt hlt]

theorem posObs_presence_invariant (hide : FillHidden X.S X.prf) (τ : Traffic Msg) (p₁ p₂ : Presences)
    (duty : X.PresenceAgreesAtDutyTicks p₁ p₂) (k : Nat) {ρ : Nat} (hρ : ρ < X.sched.n) :
    X.cellObs (X.sched.assembleAt X.prf (X.epochOf k) (X.tickOf k) (X.received τ p₁ k) ρ).1 =
      X.cellObs (X.sched.assembleAt X.prf (X.epochOf k) (X.tickOf k) (X.received τ p₂ k) ρ).1 := by
  have e₁ := congrArg Prod.fst (X.posObs_run τ p₁ k hρ)
  have e₂ := congrArg Prod.fst (X.posObs_run τ p₂ k hρ)
  simp only at e₁ e₂
  rw [e₁, e₂]
  by_cases ht : X.tickOf k = 0
  · rw [show X.emittedObs τ p₁ k ρ = X.emittedObs τ p₂ k ρ by simp [emittedObs, emitted, duty k ρ ht]]
  · have hreg : isDutyTick (X.hdr k ρ) = false := by simp [X.hdr_isDutyTick, ht]
    -- each side is either the holder's sealed cell or the fill, and the two observe alike
    have side : ∀ q : Presences, (match X.emittedObs τ q k ρ with
        | some x => (x.2.2, Source.holder x.1)
        | none => (⟨X.hdr k ρ, X.sched.profile.C, X.S.observe (X.hdr k ρ) (fit _ (X.prf (X.hdr k ρ)))⟩, .fill)).1 =
          (⟨X.hdr k ρ, X.sched.profile.C, X.S.observe (X.hdr k ρ) (fit _ (X.prf (X.hdr k ρ)))⟩ : CellObs Obs) := by
      intro q
      unfold emittedObs emitted
      cases hs : X.sched.holderOf (X.epochOf k) ρ with
      | none => rfl
      | some s =>
        by_cases hq : q k ρ = true
        · cases hem : X.em (τ k ρ) with
          | none => simp [hq]
          | some off =>
            simp only [hq, ↓reduceIte, Option.map_some, X.cellObs_ofRaw]
            rw [hide s (X.hdr k ρ) (τ k ρ) hreg]
        · simp [hq]
    rw [side p₁, side p₂]

/-- **`member_view_independent_of_presence`** (CHANNELS.md §2.4, revision 2). Fix the membership and the
traffic. When the relay fills absent positions and keeps the mask from members (`RelayFills`), fans
out to every slot every tick (`ConstantFanout`), the fill half of the sealing hypothesis holds, and
presence agrees at duty ticks, a non-recipient member's trace does not depend on who else is online. -/
theorem member_view_independent_of_presence (pol : RelayPolicy) (fill : RelayFills pol) (fan : ConstantFanout pol)
    (hide : FillHidden X.S X.prf) (τ : Traffic Msg) (p₁ p₂ : Presences)
    (duty : X.PresenceAgreesAtDutyTicks p₁ p₂) (me ticks : Nat) :
    trace (X.memberTick pol τ p₁ me) ticks = trace (X.memberTick pol τ p₂ me) ticks := by
  apply List.map_congr_left
  intro k _
  have hfills : pol.fills = true := fill.1
  have hmask : pol.maskToMembers = false := fill.2
  have hfan : pol.constantFanout = true := fan
  have del : X.delivered pol τ p₁ k = X.delivered pol τ p₂ k := by
    unfold delivered
    rw [X.tagged_eq_map, X.tagged_eq_map, List.map_map, List.map_map]
    apply List.map_congr_left
    intro ρ hρ
    simp only [Function.comp, hfills, Bool.true_or, ↓reduceIte]
    rw [X.posObs_presence_invariant hide τ p₁ p₂ duty k ((X.sched.mem_slots).1 hρ)]
  simp only [memberTick, routes, hfan, ↓reduceIte, fanout_independent_of_presence, hmask, del,
    Bool.false_eq_true]

end Domain

/-! ## Instances: satisfiable hypotheses, and every pole -/

namespace Example

open Domain

/-- A toy sealing at P1 whose observation is NOT constant. The body's first byte is a marker a
non-recipient can read — the slot at a regular tick (a stand-in for the view tag's shape, a function
of the position only), `0xD0` at a duty tick (a stand-in for the public VRF proof) — and the payload
byte follows it. A non-recipient observes the first byte. -/
def marker (h : Header) : UInt8 := if isDutyTick h then 0xD0 else h.slot.val.toUInt8

def payloadBytes : Option Nat → List UInt8
  | none => []
  | some v => [v.toUInt8 + 1]

def toySeal : Sealing P1 Nat (List UInt8) where
  sealBody _ h m := fit P1.bodyLen (marker h :: payloadBytes m)
  observe _ b := b.val.take 1

/-- The relay's toy fill PRF: the slot byte first. -/
def toyPrf : FillPrf := fun h => [h.slot.val.toUInt8]

/-- The counter-instance: a "sealing" that shows the payload byte to everyone. -/
def leakySeal : Sealing P1 Nat (List UInt8) where
  sealBody := toySeal.sealBody
  observe _ b := b.val.take 2

theorem fit_take_one (x : UInt8) (l : List UInt8) : (fit P1.bodyLen (x :: l)).val.take 1 = [x] := by
  simp only [fit, List.take_take, List.cons_append]
  rw [show min 1 P1.bodyLen = 1 by decide]
  rfl

/-- **The sealing hypothesis is satisfiable** (payload half), by a non-constant observation. -/
theorem toy_payloadHidden : PayloadHidden toySeal := by
  intro s h m₁ m₂
  simp only [toySeal, fit_take_one]

/-- **The sealing hypothesis is satisfiable** (fill half). -/
theorem toy_fillHidden : FillHidden toySeal toyPrf := by
  intro s h m hreg
  simp only [toySeal, toyPrf, fit_take_one, marker, hreg, Bool.false_eq_true, ↓reduceIte]

theorem leaky_not_payloadHidden : ¬ PayloadHidden leakySeal := by
  intro h
  have := h 10 (sched.headerAt 0 1 0) none (some 5)
  revert this
  decide +kernel

/-- The channel: `sched` (P1, slot 0 → subject 10, slot 1 → subject 11, slot 2 unleased),
the toy sealing, the toy fill, the design's emission rule. -/
def toy : Domain Nat (List UInt8) :=
  { sched := sched, S := toySeal, prf := toyPrf, em := designEmission P1 Nat }

def leaky : Domain Nat (List UInt8) := { toy with S := leakySeal }

def onDemand : Domain Nat (List UInt8) := { toy with em := fun m => m.map fun _ => 700 }

/-- Slot 0 is held by subject 12 instead of 10: a different membership. -/
def otherMembers : Domain Nat (List UInt8) :=
  { toy with
    sched := { sched with
      leases := [⟨⟨7, by decide⟩, 12, 0, P1, (0, 5)⟩, ⟨⟨7, by decide⟩, 11, 1, P1, (0, 5)⟩] } }

/-- All padding. -/
def quiet : Traffic Nat := fun _ _ => none
/-- Slot 0 sends payload 5 at tick 1. -/
def chatty : Traffic Nat := fun k ρ => if k == 1 && ρ == 0 then some 5 else none

def allOn : Presences := fun _ _ => true
/-- Slot 1's holder offline at tick 1 (a regular tick). -/
def slot1OffRegular : Presences := fun k ρ => !(k == 1 && ρ == 1)
/-- Slot 1's holder offline at tick 0 (the duty tick). -/
def slot1OffDuty : Presences := fun k ρ => !(k == 0 && ρ == 1)

/-! ### `observable_trace_depends_only_on_membership`: a non-vacuous instance -/

/-- The hypotheses hold on `toy`, the traffics genuinely differ, and the CELLS differ (a recipient
reads 5)… -/
theorem toy_cells_differ : (toy.tagged quiet allOn 1).map Prod.fst ≠ (toy.tagged chatty allOn 1).map Prod.fst := by
  decide +kernel

/-- …yet every non-recipient observer's trace is equal (the theorem, instantiated). -/
theorem toy_traces_equal :
    trace (toy.wireTick designPolicy quiet allOn) 2 = trace (toy.wireTick designPolicy chatty allOn) 2 ∧
    trace (toy.relayTick quiet allOn) 2 = trace (toy.relayTick chatty allOn) 2 :=
  let r := toy.observable_trace_depends_only_on_membership toy_payloadHidden (designEmission_constant P1 Nat)
    designPolicy quiet chatty allOn 2 2
  ⟨r.1, r.2.1⟩

/-! ### Its poles -/

/-- Without `ConstantEmission` (emit only with payload): the wire sees the first payload. -/
theorem onDemand_breaks_membership_theorem :
    trace (onDemand.wireTick designPolicy quiet allOn) 2 ≠ trace (onDemand.wireTick designPolicy chatty allOn) 2 ∧
    trace (onDemand.relayTick quiet allOn) 2 ≠ trace (onDemand.relayTick chatty allOn) 2 := by
  decide +kernel

/-- Without `PayloadHidden`: same emission, same schedule, and the wire reads the payload. -/
theorem leaky_breaks_membership_theorem :
    trace (leaky.wireTick designPolicy quiet allOn) 2 ≠ trace (leaky.wireTick designPolicy chatty allOn) 2 := by
  decide +kernel

/-- **The presence leak** (limit 4): differing presence is visible to the wire, the relay, the operator
and the witnesses, whatever the traffic. -/
theorem presence_visible_to_wire_relay_operator_witness :
    trace (toy.wireTick designPolicy quiet allOn) 2 ≠ trace (toy.wireTick designPolicy quiet slot1OffRegular) 2 ∧
    trace (toy.relayTick quiet allOn) 2 ≠ trace (toy.relayTick quiet slot1OffRegular) 2 ∧
    trace (toy.operatorTick quiet allOn) 2 ≠ trace (toy.operatorTick quiet slot1OffRegular) 2 ∧
    trace (toy.witnessTick quiet allOn) 2 ≠ trace (toy.witnessTick quiet slot1OffRegular) 2 := by
  decide +kernel

/-- **Membership is visible**: change who holds slot 0 and the wire's trace differs (the access link that
emits is another subject's). -/
theorem membership_visible_to_wire :
    trace (toy.wireTick designPolicy quiet allOn) 2 ≠ trace (otherMembers.wireTick designPolicy quiet allOn) 2 := by
  decide +kernel

/-! ### `member_view_independent_of_presence`: a non-vacuous instance -/

/-- The relay sees slot 1 go offline… -/
theorem relay_sees_presence_change :
    trace (toy.relayTick chatty allOn) 2 ≠ trace (toy.relayTick chatty slot1OffRegular) 2 := by
  decide +kernel

/-- Slot 1's absence at tick 1 is at a regular tick. -/
theorem toy_duty_agree : toy.PresenceAgreesAtDutyTicks allOn slot1OffRegular := by
  intro k ρ hk
  have hk' : k % 16 = 0 := hk
  have : k ≠ 1 := by rintro rfl; exact absurd hk' (by decide)
  simp [allOn, slot1OffRegular, this]

/-- …and member 2 (a non-recipient) does not (the theorem, instantiated: `toy_fillHidden` and duty-tick
agreement discharged). -/
theorem member_blind_to_presence_change :
    trace (toy.memberTick designPolicy chatty allOn 2) 2 = trace (toy.memberTick designPolicy chatty slot1OffRegular 2) 2 :=
  toy.member_view_independent_of_presence designPolicy designPolicy_fills designPolicy_constantFanout toy_fillHidden
    chatty allOn slot1OffRegular toy_duty_agree 2 2

/-! ### Its poles -/

/-- Pole (i): a member-readable absent mask (fill kept, mask published). -/
theorem readable_mask_reveals_presence :
    trace (toy.memberTick ⟨true, true, true⟩ chatty allOn 2) 2 ≠
      trace (toy.memberTick ⟨true, true, true⟩ chatty slot1OffRegular 2) 2 := by
  decide +kernel

/-- Pole (ii): presence-dependent fan-out — member 2's copy moves up the send order when slot 1 is
offline, so its receipt time betrays how many are online. -/
theorem connected_fanout_reveals_presence :
    trace (toy.memberTick ⟨true, false, false⟩ chatty allOn 2) 2 ≠
      trace (toy.memberTick ⟨true, false, false⟩ chatty slot1OffRegular 2) 2 := by
  decide +kernel

/-- Pole (iii): no fill (absent positions delivered as absent, mask hidden). -/
theorem no_fill_reveals_presence :
    trace (toy.memberTick ⟨false, false, true⟩ chatty allOn 2) 2 ≠
      trace (toy.memberTick ⟨false, false, true⟩ chatty slot1OffRegular 2) 2 := by
  decide +kernel

/-- Pole (iv): presence differing at a duty tick reaches members under the full design: the fill
cannot carry the holder's VRF proof. -/
theorem fill_distinguishable_at_duty_tick :
    trace (toy.memberTick designPolicy chatty allOn 2) 2 ≠ trace (toy.memberTick designPolicy chatty slot1OffDuty 2) 2 := by
  decide +kernel

end Example


end Minidregg.Theory.Channel
