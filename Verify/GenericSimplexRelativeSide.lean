import Verify.GenericSimplexRelativeReach
import Kernel.GenericSimplexRebaseMeets
import Kernel.GenericSimplexOutbox

/-! One correct running replica against the trail of its run.

`Side` is what the induction over a run of running replicas (`RelReachable`) keeps for each
correct member: its specification state with retained audit (`GenericSimplexTrail.Ghost`),
whose forgotten image is the replica's own state; the replica's height and digest are its
chain's; every wire message it has written, read as a whole chain (`denote`), is a SEND of
the trail and states the chain it is for (`Own`); and every SEND of this member in the trail
is in its durable record or still queued.

`Ran` is a run of specification steps on that state between two drains of its outbox.
`side_finish` is the replica's `finish` after such a run: the outputs leave in wire form and
the origin moves if the run committed (`ghost_rebase`, through `rebased_meets`). -/
namespace Minidregg.Verify.GenericSimplexRelativeSide
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexRelative
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexCausal
open Minidregg.Kernel.GenericSimplexPreparedHistory
open Minidregg.Kernel.GenericSimplexPositive
open Minidregg.Kernel.GenericSimplexOutputHistory
open Minidregg.Kernel.GenericSimplexReceiveScope
open Minidregg.Kernel.GenericSimplexStructure
open Minidregg.Kernel.GenericSimplexFresh
open Minidregg.Kernel.GenericSimplexTrail
open Minidregg.Kernel.GenericSimplexRebaseGhost
open Minidregg.Kernel.GenericSimplexRebaseMeets
open Minidregg.Kernel.GenericSimplexTip
open Minidregg.Kernel.GenericSimplexOutbox
open Minidregg.Kernel.GenericSimplexFloor (FloorInvariant step_floor floor_of_same)
open Minidregg.Kernel.GenericSimplexErasure (liveStep_forget)
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Verify.GenericSimplexRelativeReach (denote)
set_option autoImplicit false

/-! ## A member's own wire message -/

/-- A wire message as its sender's own, against the chain the sender has committed: it was
written from within that chain, the whole-chain message it denotes is a SEND of the trail,
and a COMMIT states the length and digest of the chain it is for. -/
def Own (h : ChainDigest) (trail : List Event) (chain : Block) (w : WireMessage) : Prop :=
  w.height ≤ chain.length ∧ (.send (denote chain w) : Event) ∈ trail ∧
    (w.kind = .commit →
      w.statement = (denote chain w).value.map fun whole => (whole.length, h.of whole))

theorem denote_append (chain more : Block) (w : WireMessage) (within : w.height ≤ chain.length) :
    denote (chain ++ more) w = denote chain w := by
  unfold denote
  rw [List.take_append_of_le_length within]

theorem own_mono {h : ChainDigest} {trail trail' : List Event} {chain : Block} {w : WireMessage}
    (own : Own h trail chain w) (grows : ∀ e ∈ trail, e ∈ trail') (more : Block) :
    Own h trail' (chain ++ more) w := by
  obtain ⟨within, sent, stated⟩ := own
  refine ⟨by rw [List.length_append]; omega, ?_, ?_⟩
  · rw [denote_append _ _ _ within]; exact grows _ sent
  · rw [denote_append _ _ _ within]; exact stated

theorem denote_encode (h : ChainDigest) (chain pre : Block) (digest : Bytes) (m : Message)
    (isPre : pre <+: chain) : denote chain (encode h pre.length digest m) = liftMessage pre m := by
  have same : chain.take pre.length = pre := (List.prefix_iff_eq_take.mp isPre).symm
  simp only [denote, encode, liftMessage, liftArgument, same]

/-- A message written from a prefix of the chain, with that prefix's digest. -/
theorem own_encode {h : ChainDigest} {trail : List Event} {chain pre : Block} {digest : Bytes}
    {m : Message} (isPre : pre <+: chain) (tracks : digest = h.of pre)
    (sent : (.send (liftMessage pre m) : Event) ∈ trail) :
    Own h trail chain (encode h pre.length digest m) := by
  refine ⟨isPre.length_le, by rw [denote_encode h chain pre digest m isPre]; exact sent, ?_⟩
  intro commit
  rw [denote_encode h chain pre digest m isPre]
  obtain ⟨sender, view, kind, value⟩ := m
  have kindC : kind = .commit := commit
  subst kindC
  cases value with
  | none => rfl
  | some run =>
    simp only [encode, liftMessage, liftArgument, Option.map, tracks, ChainDigest.of,
      ChainDigest.over_append, List.length_append]
    rfl

/-! ## Changing fields no invariant reads -/

theorem ghost_same {c : Config} {faulty : Finset Nat} {p base : Nat} {chain : Block}
    {trail : List Event} {G G' : State} (ghost : Ghost c faulty p base chain trail G)
    (self : G'.self = G.self) (views : G'.views = G.views) (audit : G'.audit = G.audit)
    (delivered : G'.delivered = G.delivered) (current : G'.current = G.current)
    (floor : G'.lastCommitted = G.lastCommitted) (evidence : G'.floorEvidence = G.floorEvidence) :
    Ghost c faulty p base chain trail G' :=
  { self := self.trans ghost.self
    causal := causal_same_fields G G' ghost.causal self views audit
    history := history_same_fields G G' ghost.history self views audit
    origins := audit ▸ ghost.origins
    positive := by
      have old := ghost.positive
      unfold Positive at old ⊢
      rw [current, views, audit]
      exact old
    scope := by
      have old := ghost.scope
      unfold Scoped at old ⊢
      rw [self, views]
      exact old
    output := output_same_fields G G' ghost.output self views audit delivered
    owned := by
      have old := ghost.owned
      unfold OwnedAudit at old ⊢
      rw [self, audit]
      exact old
    live := by rw [floor, current]; exact ghost.live
    baseLe := by rw [floor]; exact ghost.baseLe
    committed := ghost.committed
    embed := by rw [audit]; exact ghost.embed
    received := by rw [views]; exact ghost.received
    complete := by rw [floor, audit]; exact ghost.complete
    evidenceViews := by rw [floor, evidence]; exact ghost.evidenceViews }

theorem viewAt_same {G G' : State} (views : G'.views = G.views) (n : Nat) :
    viewAt G' n = viewAt G n := by
  unfold viewAt
  rw [views]

/-! ## A run of steps between two drains -/

/-- From `G` with trail `trail`, some steps of the specification have led to `G1` with
trail `trail1`, the replica's committed chain staying `chain`. `out`, `fresh`: the outbox
and this member's new SENDs of the trail are the same messages. `relay`: what is owed to a
peer is the old floor evidence, or is for a view above the old floor and in the trail.
`evident`: the floor evidence is the old one, or the floor rose and it is in the trail. -/
structure Ran (c : Config) (faulty : Finset Nat) (p base : Nat) (chain : Block)
    (trail : List Event) (G : State) (trail1 : List Event) (G1 : State) : Prop where
  ghost : Ghost c faulty p base chain trail1 G1
  good : Good c faulty trail1
  floor : FloorInvariant G1
  tipped : Tipped G1
  grows : ∃ extra, trail1 = trail ++ extra ∧
    ∀ m, (.send m : Event) ∈ extra → m.sender = p ∨ m.sender ∈ faulty
  out : ∀ m ∈ G1.outbox, m ∈ G.outbox ∨ (.send (liftMessage chain m) : Event) ∈ trail1
  fresh : ∀ m, (.send m : Event) ∈ trail1 → m.sender = p →
    (.send m : Event) ∈ trail ∨ ∃ m0 ∈ G1.outbox, liftMessage chain m0 = m
  relay : ∀ x ∈ G1.relay, x ∈ G.relay ∨ (x.2.view ≤ G.lastCommitted ∧ x.2 ∈ G.floorEvidence) ∨
    (G.lastCommitted < x.2.view ∧ (.send (liftMessage chain x.2) : Event) ∈ trail1)
  evident : (G1.lastCommitted = G.lastCommitted ∧ G1.floorEvidence = G.floorEvidence) ∨
    (G.lastCommitted < G1.lastCommitted ∧ ∀ m ∈ G1.floorEvidence,
      G.lastCommitted < m.view ∧ (.send (liftMessage chain m) : Event) ∈ trail1)

theorem ran_refl {c : Config} {faulty : Finset Nat} {p base : Nat} {chain : Block}
    {trail : List Event} {G : State} (ghost : Ghost c faulty p base chain trail G)
    (good : Good c faulty trail) (floor : FloorInvariant G) (tipped : Tipped G) :
    Ran c faulty p base chain trail G trail G :=
  { ghost := ghost, good := good, floor := floor, tipped := tipped
    grows := ⟨[], (List.append_nil _).symm, fun m member => by cases member⟩
    out := fun m member => Or.inl member
    fresh := fun m member _ => Or.inl member
    relay := fun x member => Or.inl member
    evident := Or.inl ⟨rfl, rfl⟩ }

/-- Fields no invariant reads may change after a run. -/
theorem ran_same {c : Config} {faulty : Finset Nat} {p base : Nat} {chain : Block}
    {trail trail1 : List Event} {G G1 G1' : State} (ran : Ran c faulty p base chain trail G trail1 G1)
    (self : G1'.self = G1.self) (views : G1'.views = G1.views) (audit : G1'.audit = G1.audit)
    (delivered : G1'.delivered = G1.delivered) (current : G1'.current = G1.current)
    (floor : G1'.lastCommitted = G1.lastCommitted) (evidence : G1'.floorEvidence = G1.floorEvidence)
    (outbox : G1'.outbox = G1.outbox) (relay : G1'.relay = G1.relay)
    (tip : G1'.committedTip = G1.committedTip) :
    Ran c faulty p base chain trail G trail1 G1' :=
  { ghost := ghost_same ran.ghost self views audit delivered current floor evidence
    good := ran.good
    floor := floor_of_same G1 G1' ran.floor floor (fun n => by rw [viewAt_same views])
    tipped := tip_of_same G1 G1' ran.tipped tip (fun n => by rw [viewAt_same views])
    grows := ran.grows
    out := by rw [outbox]; exact ran.out
    fresh := by rw [outbox]; exact ran.fresh
    relay := by rw [relay]; exact ran.relay
    evident := by rw [floor, evidence]; exact ran.evident }

theorem ran_floor {c : Config} {faulty : Finset Nat} {p base : Nat} {chain : Block}
    {trail trail1 : List Event} {G G1 : State} (ran : Ran c faulty p base chain trail G trail1 G1) :
    G.lastCommitted ≤ G1.lastCommitted := by
  rcases ran.evident with ⟨same, _⟩ | ⟨rose, _⟩ <;> omega

/-- **One more step of the run.** -/
theorem ran_step {c : Config} {faulty : Finset Nat} {p base : Nat} {chain : Block}
    {trail trail1 : List Event} {G G1 : State} (ran : Ran c faulty p base chain trail G trail1 G1)
    (honest : p ∉ faulty) (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults)
    (input : Input)
    (available : Readable (fun m => (.send (liftMessage chain m) : Event) ∈ trail1)
      G1.lastCommitted input) :
    ∃ fresh : List Event,
      Ran c faulty p base chain trail G (trail1 ++ fresh.map (liftEvent chain)) (step c G1 input) := by
  obtain ⟨fresh, audit, ghost2, good2, owners, sendsOut, outboxSrc⟩ :=
    ghost_step input ran.ghost ran.good honest size faultBound available
  have floorLe := ran_floor ran
  have old : ∀ e ∈ trail1, e ∈ trail1 ++ fresh.map (liftEvent chain) :=
    fun e member => List.mem_append.mpr (Or.inl member)
  have again : ∀ m, (.send m : Event) ∈ trail1 → m.sender = p →
      (.send m : Event) ∈ trail ∨ ∃ m0 ∈ (step c G1 input).outbox, liftMessage chain m0 = m := by
    intro m member own
    rcases ran.fresh m member own with before | ⟨m0, queued, same⟩
    · exact Or.inl before
    · exact Or.inr ⟨m0, step_kept c G1 input (fun _ inside => inside) m0 queued, same⟩
  refine ⟨fresh, ?_⟩
  exact
    { ghost := ghost2
      good := good2
      floor := step_floor c G1 input ran.floor
      tipped := step_tip c G1 input ran.tipped
      grows := by
        obtain ⟨extra, named, foreign⟩ := ran.grows
        refine ⟨extra ++ fresh.map (liftEvent chain), by rw [named, List.append_assoc], ?_⟩
        intro m member
        rcases List.mem_append.mp member with inside | added
        · exact foreign m inside
        · obtain ⟨event, isNew, lifted⟩ := List.mem_map.mp added
          obtain ⟨value, named, _⟩ := liftEvent_send lifted
          have owner := owners event isNew
          rw [named] at owner
          simp only [eventOwner, Option.some.injEq] at owner
          exact Or.inl owner
      out := by
        intro m member
        rcases outboxSrc m member with queued | sent
        · exact (ran.out m queued).imp id (old _)
        · exact Or.inr sent
      fresh := by
        intro m member own
        rcases List.mem_append.mp member with inside | added
        · exact again m inside own
        · obtain ⟨event, isNew, lifted⟩ := List.mem_map.mp added
          obtain ⟨value, named, same⟩ := liftEvent_send lifted
          rcases sendsOut _ (named ▸ isNew) with queued | before
          · refine Or.inr ⟨_, queued, ?_⟩
            obtain ⟨sender, view, kind, arg⟩ := m
            simp only [liftMessage] at same ⊢
            rw [same]
          · have whole : liftMessage chain ⟨m.sender, m.view, m.kind, value⟩ = m := by
              obtain ⟨sender, view, kind, arg⟩ := m
              simp only [liftMessage] at same ⊢
              rw [same]
            rw [whole] at before
            exact again m before own
      relay := by
        intro x member
        rcases step_relay c G1 input ran.ghost.causal ran.ghost.live x member with
          queued | evidence | ⟨_, number, above, received⟩
        · rcases ran.relay x queued with a | b | ⟨high, sent⟩
          · exact Or.inl a
          · exact Or.inr (Or.inl b)
          · exact Or.inr (Or.inr ⟨high, old _ sent⟩)
        · rcases ran.evident with ⟨sameFloor, sameEvidence⟩ | ⟨_, each⟩
          · have low := ran.ghost.evidenceViews x.2 evidence
            exact Or.inr (Or.inl ⟨by omega, sameEvidence ▸ evidence⟩)
          · obtain ⟨high, sent⟩ := each x.2 evidence
            exact Or.inr (Or.inr ⟨high, old _ sent⟩)
        · have named := (viewAt_scoped ran.ghost.scope number x.2 received).2
          obtain ⟨view, stored, inside⟩ := viewAt_mem received
          exact Or.inr (Or.inr ⟨by omega, old _ (ran.ghost.received view stored x.2 inside)⟩)
      evident := by
        rcases step_evident c G1 input with ⟨sameFloor, sameEvidence⟩ | ⟨rose, inside⟩
        · rcases ran.evident with ⟨f, e⟩ | ⟨r, each⟩
          · exact Or.inl ⟨sameFloor.trans f, sameEvidence.trans e⟩
          · refine Or.inr ⟨by omega, fun m member => ?_⟩
            obtain ⟨high, sent⟩ := each m (sameEvidence ▸ member)
            exact ⟨high, old _ sent⟩
        · refine Or.inr ⟨by omega, fun m member => ?_⟩
          have named := (viewAt_scoped ghost2.scope _ m (inside m member)).2
          obtain ⟨view, stored, held⟩ := viewAt_mem (inside m member)
          exact ⟨by omega, ghost2.received view stored m held⟩ }

/-! ## The wire side of a replica -/

/-- What a replica has written, against the trail. `durable` is the chain at its last
drain and `chain` the chain now (`pending`). `sent` is its durable record; `sends`, `owed`,
`evidence` are the replica's queues and kept COMMIT evidence. `only`: every SEND of this
member in the trail is in the record or queued. `evidence`, `origin`: kept evidence, and
the floor evidence, are written from a prefix of the chain and their messages of this
member are SENDs of the trail read from that prefix. -/
structure Wire (h : ChainDigest) (p : Nat) (trail : List Event) (durable chain : Block)
    (record : List (Block × WireMessage)) (floorEvidence : List Message)
    (done : Block) (level : Nat) (mark : Bytes) (queue : List WireMessage)
    (debts : List (Nat × WireMessage)) (kept : List (Nat × Bytes × List Message)) : Prop where
  pending : chain = durable ++ done
  height : level = chain.length
  digest : mark = h.of chain
  sent : ∀ entry ∈ record, entry.2.sender = p → Own h trail entry.1 entry.2
  sends : ∀ w ∈ queue, w.sender = p → Own h trail chain w
  owed : ∀ x ∈ debts, x.2.sender = p → Own h trail chain x.2
  only : ∀ m, (.send m : Event) ∈ trail → m.sender = p →
    (∃ entry ∈ record, denote entry.1 entry.2 = m) ∨ ∃ w ∈ queue, denote chain w = m
  evidence : ∀ entry ∈ kept, ∃ pre, pre <+: chain ∧ entry.1 = pre.length ∧
    entry.2.1 = h.of pre ∧
    ∀ m ∈ entry.2.2, m.sender = p → (.send (liftMessage pre m) : Event) ∈ trail
  origin : ∃ pre, pre <+: chain ∧
    (kept.getLast?.map fun entry => (entry.1, entry.2.1)).getD (0, h.origin) = (pre.length, h.of pre) ∧
    ∀ m ∈ floorEvidence, m.sender = p → (.send (liftMessage pre m) : Event) ∈ trail

/-- One correct running replica against the trail: its specification state, and its wire side. -/
structure Side (c : Config) (h : ChainDigest) (faulty : Finset Nat) (p base : Nat) (G : State)
    (trail : List Event) (durable chain : Block) (sent : List (Block × WireMessage))
    (r : Replica) : Prop where
  ghost : Ghost c faulty p base chain trail G
  floor : FloorInvariant G
  tipped : Tipped G
  core : r.core = forget G
  quiet : G.outbox = [] ∧ G.relay = []
  wire : Wire h p trail durable chain sent G.floorEvidence r.committed r.height r.digest r.sends
    r.owed r.evidence

theorem own_trail {h : ChainDigest} {trail trail' : List Event} {chain : Block} {w : WireMessage}
    (own : Own h trail chain w) (grows : ∀ e ∈ trail, e ∈ trail') : Own h trail' chain w :=
  ⟨own.1, grows _ own.2.1, own.2.2⟩

/-- The trail grows by events that are not this member's SENDs, and the chain by `tip`. -/
theorem wire_grow {h : ChainDigest} {p : Nat} {trail trail' : List Event} {durable chain : Block}
    {sent : List (Block × WireMessage)} {floorEvidence : List Message}
    {committed : Block} {height : Nat} {digest : Bytes} {sends : List WireMessage}
    {owed : List (Nat × WireMessage)} {evidence : List (Nat × Bytes × List Message)}
    (wire : Wire h p trail durable chain sent floorEvidence committed height digest sends owed evidence)
    (grows : ∀ e ∈ trail, e ∈ trail')
    (foreign : ∀ m, (.send m : Event) ∈ trail' → (.send m : Event) ∈ trail ∨ m.sender ≠ p)
    (tip : Block) :
    Wire h p trail' durable (chain ++ tip) sent floorEvidence (committed ++ tip)
      (height + tip.length) (h.over digest tip) sends owed evidence :=
  { pending := by rw [wire.pending, List.append_assoc]
    height := by rw [wire.height, List.length_append]
    digest := by rw [wire.digest, ChainDigest.of, ChainDigest.of, ChainDigest.over_append]
    sent := fun entry member own => own_trail (wire.sent entry member own) grows
    sends := fun w member own => own_mono (wire.sends w member own) grows tip
    owed := fun x member own => own_mono (wire.owed x member own) grows tip
    only := by
      intro m member own
      rcases foreign m member with before | other
      · rcases wire.only m before own with durableOne | ⟨w, queued, same⟩
        · exact Or.inl durableOne
        · have sender : w.sender = p := by rw [← own, ← same]; rfl
          exact Or.inr ⟨w, queued, by rw [denote_append _ _ _ (wire.sends w queued sender).1]; exact same⟩
      · exact absurd own other
    evidence := by
      intro entry member
      obtain ⟨pre, isPre, a, b, each⟩ := wire.evidence entry member
      exact ⟨pre, isPre.trans (List.prefix_append _ _), a, b, fun m inside own => grows _ (each m inside own)⟩
    origin := by
      obtain ⟨pre, isPre, a, each⟩ := wire.origin
      exact ⟨pre, isPre.trans (List.prefix_append _ _), a, fun m inside own => grows _ (each m inside own)⟩ }

theorem wire_extend {h : ChainDigest} {p : Nat} {trail trail' : List Event} {durable chain : Block}
    {sent : List (Block × WireMessage)} {floorEvidence : List Message}
    {committed : Block} {height : Nat} {digest : Bytes} {sends : List WireMessage}
    {owed : List (Nat × WireMessage)} {evidence : List (Nat × Bytes × List Message)}
    (wire : Wire h p trail durable chain sent floorEvidence committed height digest sends owed evidence)
    (grows : ∀ e ∈ trail, e ∈ trail')
    (foreign : ∀ m, (.send m : Event) ∈ trail' → (.send m : Event) ∈ trail ∨ m.sender ≠ p) :
    Wire h p trail' durable chain sent floorEvidence committed height digest sends owed evidence := by
  have grown := wire_grow wire grows foreign []
  simpa [ChainDigest.over] using grown

/-- Events of other members, appended to the trail, leave a replica's side as it was. -/
theorem side_extend {c : Config} {h : ChainDigest} {faulty : Finset Nat} {p base : Nat} {G : State}
    {trail : List Event} {durable chain : Block} {sent : List (Block × WireMessage)} {r : Replica}
    (side : Side c h faulty p base G trail durable chain sent r) (extra : List Event)
    (others : ∀ m, (.send m : Event) ∈ extra → m.sender ≠ p) :
    Side c h faulty p base G (trail ++ extra) durable chain sent r :=
  { side with
    ghost := ghost_extend extra side.ghost others
    wire := wire_extend side.wire (fun _ member => List.mem_append.mpr (Or.inl member))
      (fun m member => (List.mem_append.mp member).imp id (others m)) }

/-! ## `finish`: the outputs leave, then the origin moves -/

/-- `finish` before the origin moves. -/
def emit (c : Config) (h : ChainDigest) (r : Replica) (core : State) : Replica :=
  { r with
    core := { core with outbox := [], relay := [] }
    sends := r.sends ++ core.outbox.map (encode h r.height r.digest)
    owed := r.owed ++ core.relay.map fun (peer, m) =>
      (peer, if m.view ≤ r.core.lastCommitted then
        encode h (r.evidenceOrigin h).1 (r.evidenceOrigin h).2 m else encode h r.height r.digest m)
    evidence :=
      if r.core.lastCommitted < core.lastCommitted then
        (r.evidence ++ [(r.height, r.digest, core.floorEvidence)]).drop
          ((r.evidence ++ [(r.height, r.digest, core.floorEvidence)]).length - c.window)
      else r.evidence }

theorem finish_eq (c : Config) (h : ChainDigest) (r : Replica) (core : State) :
    finish c h r core = rebase c h (emit c h r core) := rfl

theorem wire_emit {c : Config} {h : ChainDigest} {faulty : Finset Nat} {p base : Nat} {G G1 : State}
    {trail trail1 : List Event} {durable chain : Block} {sent : List (Block × WireMessage)}
    {r : Replica}
    (wire : Wire h p trail durable chain sent G.floorEvidence r.committed r.height r.digest r.sends
      r.owed r.evidence)
    (quiet : G.outbox = [] ∧ G.relay = []) (floorOf : r.core.lastCommitted = G.lastCommitted)
    (ran : Ran c faulty p base chain trail G trail1 G1) (window : 0 < c.window) :
    Wire h p trail1 durable chain sent G1.floorEvidence (emit c h r (forget G1)).committed
      (emit c h r (forget G1)).height (emit c h r (forget G1)).digest (emit c h r (forget G1)).sends
      (emit c h r (forget G1)).owed (emit c h r (forget G1)).evidence := by
  obtain ⟨extra, named, _⟩ := ran.grows
  have grows : ∀ e ∈ trail, e ∈ trail1 := fun e member => by
    rw [named]; exact List.mem_append.mpr (Or.inl member)
  have whole : chain <+: chain := List.prefix_refl _
  have here : r.height = chain.length := wire.height
  obtain ⟨before, beforePre, beforeNamed, beforeEach⟩ := wire.origin
  have originIs : r.evidenceOrigin h = (before.length, h.of before) := beforeNamed
  have newEntry : ∀ m ∈ G1.floorEvidence, G.lastCommitted < G1.lastCommitted →
      (.send (liftMessage chain m) : Event) ∈ trail1 := by
    intro m member rose
    rcases ran.evident with ⟨same, _⟩ | ⟨_, each⟩
    · omega
    · exact (each m member).2
  refine
    { pending := wire.pending
      height := wire.height
      digest := wire.digest
      sent := fun entry member own => own_trail (wire.sent entry member own) grows
      sends := ?_, owed := ?_, only := ?_, evidence := ?_, origin := ?_ }
  · intro w member own
    rcases List.mem_append.mp member with old | new
    · exact own_trail (wire.sends w old own) grows
    · obtain ⟨m, queued, rfl⟩ := List.mem_map.mp new
      rw [here]
      refine own_encode whole wire.digest ?_
      rcases ran.out m queued with impossible | inTrail
      · rw [quiet.1] at impossible; cases impossible
      · exact inTrail
  · intro x member own
    rcases List.mem_append.mp member with old | new
    · exact own_trail (wire.owed x old own) grows
    · obtain ⟨⟨peer, m⟩, queued, rfl⟩ := List.mem_map.mp new
      have sender : m.sender = p := by
        dsimp only at own
        split at own <;> exact own
      dsimp only
      rcases ran.relay (peer, m) queued with impossible | ⟨low, kept⟩ | ⟨high, inTrail⟩
      · rw [quiet.2] at impossible; cases impossible
      · rw [ite_eq_left (by rw [floorOf]; exact low), originIs]
        exact own_encode beforePre rfl (grows _ (beforeEach m kept sender))
      · rw [ite_eq_right (by rw [floorOf]; dsimp only at high; omega), here]
        exact own_encode whole wire.digest inTrail
  · intro m member own
    rcases ran.fresh m member own with before | ⟨m0, queued, same⟩
    · rcases wire.only m before own with durableOne | ⟨w, held, named⟩
      · exact Or.inl durableOne
      · exact Or.inr ⟨w, List.mem_append.mpr (Or.inl held), named⟩
    · refine Or.inr ⟨encode h r.height r.digest m0,
        List.mem_append.mpr (Or.inr (List.mem_map_of_mem queued)), ?_⟩
      rw [here, denote_encode h chain chain _ m0 whole]
      exact same
  · intro entry member
    have old : ∀ entry ∈ r.evidence, ∃ pre, pre <+: chain ∧ entry.1 = pre.length ∧
        entry.2.1 = h.of pre ∧
        ∀ m ∈ entry.2.2, m.sender = p → (.send (liftMessage pre m) : Event) ∈ trail1 := by
      intro entry inside
      obtain ⟨pre, isPre, a, b, each⟩ := wire.evidence entry inside
      exact ⟨pre, isPre, a, b, fun m held own => grows _ (each m held own)⟩
    unfold emit at member
    dsimp only at member
    split at member
    · rename_i rose
      rw [floorOf] at rose
      rcases List.mem_append.mp (List.mem_of_mem_drop member) with inside | added
      · exact old entry inside
      · rw [List.mem_singleton] at added
        subst added
        exact ⟨chain, whole, here, wire.digest, fun m held _ => newEntry m held rose⟩
    · exact old entry member
  · unfold emit
    dsimp only
    split
    · rename_i rose
      rw [floorOf] at rose
      refine ⟨chain, whole, ?_, fun m held _ => newEntry m held rose⟩
      rw [List.getLast?_drop, ite_eq_right (by rw [List.length_append, List.length_singleton]; omega),
        List.getLast?_append, List.getLast?_singleton]
      simp [here, wire.digest]
    · rename_i same
      rw [floorOf] at same
      refine ⟨before, beforePre, beforeNamed, ?_⟩
      rcases ran.evident with ⟨_, sameEvidence⟩ | ⟨rose, _⟩
      · intro m held own
        exact grows _ (beforeEach m (sameEvidence ▸ held) own)
      · exact absurd rose same

theorem rebase_shape (c : Config) (h : ChainDigest) (r : Replica) : rebase c h r =
    if r.core.committedTip.isEmpty then r else
    match r.core.views.mapM (rebaseKept c r.core.self r.core.lastCommitted r.core.committedTip) with
    | none => { r with core := { r.core with failed := true } }
    | some views =>
      { r with
        core := { r.core with
          views, checked := r.core.checked.filterMap (strip (applicationHistory r.core.committedTip)),
          committedTip := [], delivered := [] }
        height := r.height + r.core.committedTip.length
        records := r.records + (applicationHistory r.core.committedTip).length
        digest := h.over r.digest r.core.committedTip
        committed := r.committed ++ r.core.committedTip } := rfl

/-- **The origin moves.** If the run committed and the replica's map over its views
succeeds, its side holds over the longer chain; otherwise the replica is as it was (halted,
if the map failed). -/
theorem side_rebase {c : Config} {h : ChainDigest} {faulty : Finset Nat} {p base : Nat} {G : State}
    {trail : List Event} {durable chain : Block} {sent : List (Block × WireMessage)} {r : Replica}
    (side : Side c h faulty p base G trail durable chain sent r) (good : Good c faulty trail)
    (honest : p ∉ faulty) (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults) :
    ∃ extra base' G', (∀ m, (.send m : Event) ∈ extra → m.sender ∈ faulty) ∧
      Good c faulty (trail ++ extra) ∧
      Side c h faulty p base' G' (trail ++ extra) durable (durable ++ (rebase c h r).committed) sent
        (rebase c h r) := by
  obtain ⟨rcore, rheight, rdigest, rrecords, revidence, rfar, rsends, rowed, rcommitted⟩ := r
  have core : rcore = forget G := side.core
  subst core
  have pend := side.wire.pending
  dsimp only at pend
  rw [rebase_shape]
  dsimp only
  split
  · refine ⟨[], base, G, (by simp), by rw [List.append_nil]; exact good, ?_⟩
    rw [List.append_nil, ← pend]
    exact side
  · rename_i nonEmpty
    have empty : G.committedTip ≠ [] := fun same => nonEmpty (by
      show G.committedTip.isEmpty = true
      rw [same]; rfl)
    split
    · refine ⟨[], base, { G with failed := true }, (by simp),
        by rw [List.append_nil]; exact good, ?_⟩
      rw [List.append_nil, ← pend]
      exact
        { ghost := ghost_same side.ghost rfl rfl rfl rfl rfl rfl rfl
          floor := floor_of_same G _ side.floor rfl (fun _ => rfl)
          tipped := tip_of_same G _ side.tipped rfl (fun _ => rfl)
          core := rfl
          quiet := side.quiet
          wire := side.wire }
    · rename_i views heq
      have mapped : (G.views.filter fun v => G.lastCommitted ≤ v.number).mapM
          (rebaseKept c G.self G.lastCommitted G.committedTip) = some views := heq
      obtain ⟨rebased, live, floor', tipped'⟩ := rebased_meets
        (G.checked.filterMap (strip (applicationHistory G.committedTip)))
        side.ghost.causal.viewsUnique side.floor side.tipped empty mapped
      obtain ⟨extra, faultyOnly, ghost', good'⟩ :=
        ghost_rebase side.ghost good honest size faultBound rebased
      refine ⟨extra, G.lastCommitted, ghostAfter G views
        (G.checked.filterMap (strip (applicationHistory G.committedTip))), faultyOnly, good', ?_⟩
      have grown := wire_grow side.wire (fun _ member => List.mem_append.mpr (Or.inl member))
        (fun m member => (List.mem_append.mp member).imp id
          (fun added own => honest (own ▸ faultyOnly m added))) G.committedTip
      have keep : views.filter (fun v => G.lastCommitted ≤ v.number) = views :=
        List.filter_eq_self.mpr (fun v member => decide_eq_true (live v member))
      have whole : durable ++ (rcommitted ++ G.committedTip) = chain ++ G.committedTip := by
        rw [pend, List.append_assoc]
      show Side _ _ _ _ _ _ _ _ (durable ++ (rcommitted ++ G.committedTip)) _ _
      rw [whole]
      exact
        { ghost := ghost'
          floor := floor'
          tipped := tipped'
          core := by
            show _ = forget (ghostAfter G views _)
            unfold forget ghostAfter
            dsimp only
            rw [keep]
          quiet := side.quiet
          wire := grown }

/-- **`finish` after a run.** -/
theorem side_finish {c : Config} {h : ChainDigest} {faulty : Finset Nat} {p base : Nat} {G G1 : State}
    {trail trail1 : List Event} {durable chain : Block} {sent : List (Block × WireMessage)}
    {r : Replica} (side : Side c h faulty p base G trail durable chain sent r)
    (ran : Ran c faulty p base chain trail G trail1 G1)
    (honest : p ∉ faulty) (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults) :
    ∃ extra base' G', (∀ m, (.send m : Event) ∈ extra → m.sender = p ∨ m.sender ∈ faulty) ∧
      Good c faulty (trail ++ extra) ∧
      Side c h faulty p base' G' (trail ++ extra) durable
        (durable ++ (finish c h r (forget G1)).committed) sent (finish c h r (forget G1)) := by
  have window : 0 < c.window := by unfold Config.window; omega
  have floorOf : r.core.lastCommitted = G.lastCommitted := by rw [side.core]; rfl
  have emitted : Side c h faulty p base { G1 with outbox := [], relay := [] } trail1 durable chain
      sent (emit c h r (forget G1)) :=
    { ghost := ghost_same ran.ghost rfl rfl rfl rfl rfl rfl rfl
      floor := floor_of_same G1 _ ran.floor rfl (fun _ => rfl)
      tipped := tip_of_same G1 _ ran.tipped rfl (fun _ => rfl)
      core := rfl
      quiet := ⟨rfl, rfl⟩
      wire := wire_emit side.wire side.quiet floorOf ran window }
  obtain ⟨extra1, named, senders⟩ := ran.grows
  obtain ⟨extra2, base', G', faultyOnly, good', side'⟩ :=
    side_rebase emitted ran.good honest size faultBound
  refine ⟨extra1 ++ extra2, base', G', ?_, ?_, ?_⟩
  · intro m member
    rcases List.mem_append.mp member with first | second
    · exact senders m first
    · exact Or.inr (faultyOnly m second)
  · rw [← List.append_assoc, ← named]; exact good'
  · rw [← List.append_assoc, ← named, finish_eq]; exact side'

theorem noteAhead_forget (s : State) (sender view : Nat) :
    noteAhead (forget s) sender view = forget (noteAhead s sender view) := by
  unfold noteAhead forget
  dsimp only
  split <;> rfl

theorem ran_ahead {c : Config} {faulty : Finset Nat} {p base : Nat} {chain : Block}
    {trail : List Event} {G : State} (ghost : Ghost c faulty p base chain trail G)
    (good : Good c faulty trail) (floor : FloorInvariant G) (tipped : Tipped G) (sender view : Nat) :
    Ran c faulty p base chain trail G trail (noteAhead G sender view) := by
  refine ran_same (ran_refl ghost good floor tipped) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (unfold noteAhead; split <;> rfl)

/-- `finish` with nothing run. -/
theorem side_idle {c : Config} {h : ChainDigest} {faulty : Finset Nat} {p base : Nat} {G : State}
    {trail : List Event} {durable chain : Block} {sent : List (Block × WireMessage)} {r : Replica}
    (side : Side c h faulty p base G trail durable chain sent r) (good : Good c faulty trail)
    (honest : p ∉ faulty) (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults) :
    ∃ extra base' G', (∀ m, (.send m : Event) ∈ extra → m.sender = p ∨ m.sender ∈ faulty) ∧
      Good c faulty (trail ++ extra) ∧
      Side c h faulty p base' G' (trail ++ extra) durable
        (durable ++ (finish c h r r.core).committed) sent (finish c h r r.core) := by
  rw [side.core]
  exact side_finish side (ran_refl side.ghost good side.floor side.tipped) honest size faultBound

/-- `finish` after noting a member ahead. -/
theorem side_noted {c : Config} {h : ChainDigest} {faulty : Finset Nat} {p base : Nat} {G : State}
    {trail : List Event} {durable chain : Block} {sent : List (Block × WireMessage)} {r : Replica}
    (side : Side c h faulty p base G trail durable chain sent r) (good : Good c faulty trail)
    (honest : p ∉ faulty) (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults)
    (sender view : Nat) :
    ∃ extra base' G', (∀ m, (.send m : Event) ∈ extra → m.sender = p ∨ m.sender ∈ faulty) ∧
      Good c faulty (trail ++ extra) ∧
      Side c h faulty p base' G' (trail ++ extra) durable
        (durable ++ (finish c h r (noteAhead r.core sender view)).committed) sent
        (finish c h r (noteAhead r.core sender view)) := by
  rw [side.core, noteAhead_forget]
  exact side_finish side (ran_ahead side.ghost good side.floor side.tipped sender view)
    honest size faultBound

/-- A delivery the trail covers: what `ingest` can record of it is a SEND of the trail, or
its sender is faulty. -/
def Covered (faulty : Finset Nat) (base : Nat) (chain : Block) (trail : List Event) (m : Message) : Prop :=
  m.kind ≠ .propose → base < m.view → (m.kind = .vote ∨ m.kind = .commit → m.value ≠ none) →
    (.send (liftMessage chain m) : Event) ∈ trail ∨ m.sender ∈ faulty

/-- The SENDs of faulty members among `messages`, read as whole chains. -/
def faultySends (faulty : Finset Nat) (chain : Block) (messages : List Message) : List Event :=
  (messages.filter fun m => decide (m.sender ∈ faulty)).map fun m => .send (liftMessage chain m)

theorem side_faulty {c : Config} {h : ChainDigest} {faulty : Finset Nat} {p base : Nat} {G : State}
    {trail : List Event} {durable chain : Block} {sent : List (Block × WireMessage)} {r : Replica}
    (side : Side c h faulty p base G trail durable chain sent r) (good : Good c faulty trail)
    (honest : p ∉ faulty) (messages : List Message) :
    Side c h faulty p base G (trail ++ faultySends faulty chain messages) durable chain sent r ∧
      Good c faulty (trail ++ faultySends faulty chain messages) ∧
      ∀ m, (.send m : Event) ∈ faultySends faulty chain messages → m.sender ∈ faulty := by
  have each : ∀ m, (.send m : Event) ∈ faultySends faulty chain messages → m.sender ∈ faulty := by
    intro m member
    obtain ⟨m0, inside, same⟩ := List.mem_map.mp member
    have bad := of_decide_eq_true (List.mem_filter.mp inside).2
    simp only [AuditEvent.send.injEq] at same
    rw [← same]
    exact bad
  refine ⟨side_extend side _ (fun m member own => honest (own ▸ each m member)), ?_, each⟩
  apply good_append_free good
  intro event member owner owned
  obtain ⟨m0, inside, same⟩ := List.mem_map.mp member
  rw [← same] at owned
  simp only [eventOwner, Option.some.injEq] at owned
  rw [← owned]
  exact of_decide_eq_true (List.mem_filter.mp inside).2

/-- **`finish` after one step of the engine.** -/
theorem side_live {c : Config} {h : ChainDigest} {faulty : Finset Nat} {p base : Nat} {G : State}
    {trail : List Event} {durable chain : Block} {sent : List (Block × WireMessage)} {r : Replica}
    (side : Side c h faulty p base G trail durable chain sent r) (good : Good c faulty trail)
    (honest : p ∉ faulty) (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults)
    (input : Input)
    (covered : ∀ m, (input = .delivery m ∨ ∃ now, input = .deliveryAt now m) →
      Covered faulty base chain trail m) :
    ∃ extra base' G', (∀ m, (.send m : Event) ∈ extra → m.sender = p ∨ m.sender ∈ faulty) ∧
      Good c faulty (trail ++ extra) ∧
      Side c h faulty p base' G' (trail ++ extra) durable
        (durable ++ (finish c h r (liveStep c r.core input)).committed) sent
        (finish c h r (liveStep c r.core input)) := by
  have delivered : ∃ messages : List Message, ∀ m,
      (input = .delivery m ∨ ∃ now, input = .deliveryAt now m) → m ∈ messages := by
    cases input with
    | delivery m => exact ⟨[m], fun x named => by rcases named with same | ⟨_, same⟩ <;> cases same; simp⟩
    | deliveryAt now m =>
      exact ⟨[m], fun x named => by rcases named with same | ⟨_, same⟩ <;> cases same; simp⟩
    | _ => exact ⟨[], fun x named => by rcases named with same | ⟨_, same⟩ <;> cases same⟩
  obtain ⟨messages, all⟩ := delivered
  obtain ⟨side0, good0, bad⟩ := side_faulty side good honest messages
  have readable : Readable
      (fun m => (.send (liftMessage chain m) : Event) ∈ trail ++ faultySends faulty chain messages)
      G.lastCommitted input := by
    have one : ∀ m, (input = .delivery m ∨ ∃ now, input = .deliveryAt now m) →
        m.kind ≠ .propose → G.lastCommitted < m.view →
        (m.kind = .vote ∨ m.kind = .commit → m.value ≠ none) →
        (.send (liftMessage chain m) : Event) ∈ trail ++ faultySends faulty chain messages := by
      intro m named kindOK above valued
      rcases covered m named kindOK (Nat.lt_of_le_of_lt side.ghost.baseLe above) valued with inside | byz
      · exact List.mem_append.mpr (Or.inl inside)
      · exact List.mem_append.mpr (Or.inr (List.mem_map_of_mem
          (List.mem_filter.mpr ⟨all m named, decide_eq_true byz⟩)))
    cases input with
    | delivery m => exact one m (Or.inl rfl)
    | deliveryAt now m => exact one m (Or.inr ⟨now, rfl⟩)
    | _ => exact True.intro
  obtain ⟨fresh, ran⟩ := ran_step (ran_refl side0.ghost good0 side0.floor side0.tipped)
    honest size faultBound input readable
  obtain ⟨extra, base', G', senders, good', side'⟩ := side_finish side0 ran honest size faultBound
  refine ⟨faultySends faulty chain messages ++ extra, base', G', ?_, ?_, ?_⟩
  · intro m member
    rcases List.mem_append.mp member with first | second
    · exact Or.inr (bad m first)
    · exact senders m second
  · rw [← List.append_assoc]; exact good'
  · rw [← List.append_assoc, side.core, liveStep_forget]; exact side'

/-! ## A delivery -/

/-- The replica after it has queued its kept evidence for a peer that asked from a lower height. -/
def answered (h : ChainDigest) (r : Replica) (w : WireMessage) : Replica :=
  if (w.kind == .candidate && w.value.isNone && w.sender != r.core.self &&
      decide (w.height < r.height) && r.evidence.any (fun entry => entry.1 == w.height)) then
    { r with owed := r.owed ++ (r.evidence.filter fun entry => w.height ≤ entry.1).flatMap fun entry =>
        entry.2.2.map fun m => (w.sender, encode h entry.1 entry.2.1 m) }
  else r

theorem deliver_shape (c : Config) (h : ChainDigest) (r : Replica) (now : Option Nat) (w : WireMessage) :
    deliver c h r now w =
      if w.sender ≥ c.parties then r else
      match decode h (answered h r w) w with
      | none =>
          if (answered h r w).height < w.height then
            finish c h { answered h r w with
              far := if w.kind == .commit then holdFar (answered h r w).far w else (answered h r w).far }
              (noteAhead r.core w.sender (max w.view (r.core.current + 1)))
          else finish c h (answered h r w) r.core
      | some m =>
          if m.kind == .commit && horizon c r.core < m.view then
            finish c h { answered h r w with far := holdFar (answered h r w).far w }
              (noteAhead r.core m.sender m.view)
          else finish c h (answered h r w) (liveStep c r.core (match now with
            | some time => .deliveryAt time m
            | none => .delivery m)) := by
  unfold deliver answered
  dsimp only
  split <;> rfl

theorem side_answered {c : Config} {h : ChainDigest} {faulty : Finset Nat} {p base : Nat} {G : State}
    {trail : List Event} {durable chain : Block} {sent : List (Block × WireMessage)} {r : Replica}
    (side : Side c h faulty p base G trail durable chain sent r) (w : WireMessage) :
    Side c h faulty p base G trail durable chain sent (answered h r w) := by
  unfold answered
  split
  · refine ⟨side.ghost, side.floor, side.tipped, side.core, side.quiet, ?_⟩
    have wire := side.wire
    refine ⟨wire.pending, wire.height, wire.digest, wire.sent, wire.sends, ?_, wire.only,
      wire.evidence, wire.origin⟩
    intro x member own
    rcases List.mem_append.mp member with old | new
    · exact wire.owed x old own
    · obtain ⟨entry, kept, inside⟩ := List.mem_flatMap.mp new
      obtain ⟨m, held, rfl⟩ := List.mem_map.mp inside
      obtain ⟨pre, isPre, a, b, each⟩ := wire.evidence entry (List.mem_of_mem_filter kept)
      rw [a]
      exact own_encode isPre b (each m held own)
  · exact side

theorem finish_far (c : Config) (h : ChainDigest) (r : Replica) (core : State) :
    (finish c h r core).far = r.far := by
  rw [finish_eq, rebase_shape]
  split
  · rfl
  · split <;> rfl

theorem holdFar_mem {far : List WireMessage} {w x : WireMessage} (member : x ∈ holdFar far w) :
    x ∈ far ∨ x = w := by
  unfold holdFar at member
  split at member
  · exact Or.inl member
  · rcases List.mem_append.mp member with kept | new
    · exact Or.inl (List.mem_of_mem_filter kept)
    · exact Or.inr (List.mem_singleton.mp new)

theorem decode_kind {h : ChainDigest} {r : Replica} {w : WireMessage} {m : Message}
    (decoded : decode h r w = some m) : m.kind = w.kind := by
  cases value : w.value with
  | none =>
    simp only [decode, value, Option.some.injEq] at decoded
    rw [← decoded]
  | some run =>
    obtain ⟨_, _, same, _⟩ := decode_some h r w m run value decoded
    rw [same]

/-- What a delivery leaves held: what was held, or the delivered COMMIT. -/
theorem deliver_far (c : Config) (h : ChainDigest) (r : Replica) (now : Option Nat) (w : WireMessage) :
    ∀ x ∈ (deliver c h r now w).far, x ∈ r.far ∨ (x = w ∧ w.kind = .commit) := by
  have same : (answered h r w).far = r.far := by unfold answered; split <;> rfl
  rw [deliver_shape]
  intro x member
  split at member
  · exact Or.inl member
  · split at member
    · split at member
      · rw [finish_far] at member
        dsimp only at member
        split at member
        · rename_i commit
          rw [same] at member
          exact (holdFar_mem member).imp id (fun named => ⟨named, beq_iff_eq.mp commit⟩)
        · exact Or.inl (same ▸ member)
      · rw [finish_far] at member
        exact Or.inl (same ▸ member)
    · rename_i m decoded
      split at member
      · rename_i beyond
        rw [finish_far] at member
        dsimp only at member
        rw [same] at member
        rw [Bool.and_eq_true] at beyond
        exact (holdFar_mem member).imp id
          (fun named => ⟨named, (decode_kind decoded).symm.trans (beq_iff_eq.mp beyond.1)⟩)
      · rw [finish_far] at member
        exact Or.inl (same ▸ member)

/-- **A delivery.** -/
theorem side_deliver {c : Config} {h : ChainDigest} {faulty : Finset Nat} {p base : Nat} {G : State}
    {trail : List Event} {durable chain : Block} {sent : List (Block × WireMessage)} {r : Replica}
    (side : Side c h faulty p base G trail durable chain sent r) (good : Good c faulty trail)
    (honest : p ∉ faulty) (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults)
    (now : Option Nat) (w : WireMessage)
    (covered : ∀ m, decode h r w = some m → Covered faulty base chain trail m) :
    ∃ extra base' G', (∀ m, (.send m : Event) ∈ extra → m.sender = p ∨ m.sender ∈ faulty) ∧
      Good c faulty (trail ++ extra) ∧
      Side c h faulty p base' G' (trail ++ extra) durable
        (durable ++ (deliver c h r now w).committed) sent (deliver c h r now w) := by
  have sideA := side_answered side w
  have coreA : (answered h r w).core = r.core := by unfold answered; split <;> rfl
  have decodeA : decode h (answered h r w) w = decode h r w := by unfold answered; split <;> rfl
  have held : ∀ far : List WireMessage,
      Side c h faulty p base G trail durable chain sent { answered h r w with far := far } :=
    fun _ => ⟨sideA.ghost, sideA.floor, sideA.tipped, sideA.core, sideA.quiet, sideA.wire⟩
  rw [deliver_shape]
  generalize answered h r w = a at sideA coreA decodeA held ⊢
  split
  · refine ⟨[], base, G, by simp, by rw [List.append_nil]; exact good, ?_⟩
    rw [List.append_nil, ← side.wire.pending]
    exact side
  · rw [decodeA]
    generalize r.core = core at coreA
    subst coreA
    split
    · split
      · exact side_noted (held _) good honest size faultBound _ _
      · exact side_idle sideA good honest size faultBound
    · rename_i m decoded
      split
      · exact side_noted (held _) good honest size faultBound _ _
      · cases now with
        | none =>
          exact side_live sideA good honest size faultBound (.delivery m) (fun x named => by
            rcases named with same | ⟨_, same⟩ <;> cases same
            exact covered m decoded)
        | some time =>
          exact side_live sideA good honest size faultBound (.deliveryAt time m) (fun x named => by
            rcases named with same | ⟨_, same⟩ <;> cases same
            exact covered m decoded)

/-! ## Releasing what was held -/

/-- The held COMMITs `release` hands the engine. -/
def releaseBatch (c : Config) (h : ChainDigest) (r : Replica) : List (WireMessage × Message) :=
  let far := r.far.filter fun w => r.core.lastCommitted < w.view
  let r := { r with far }
  let ready := far.filterMap fun w => (decode h r w).map fun m => (w, m)
  let edge := horizon c r.core
  let near := ready.filter fun (_, m) => m.view ≤ edge
  if !near.isEmpty then near
  else if r.core.views.any (fun v => edge < v.number) then []
  else match ready.find? (fun (_, m) =>
      (ready.filter fun (_, x) => x.view == m.view && x.value == m.value).length ≥ c.quorum) with
    | none => []
    | some (_, m) => ready.filter fun (_, x) => x.view == m.view && x.value == m.value

theorem release_shape (c : Config) (h : ChainDigest) (r : Replica) : release c h r =
    if (releaseBatch c h r).isEmpty then
      { r with far := r.far.filter fun w => r.core.lastCommitted < w.view }
    else finish c h { r with
        far := (r.far.filter fun w => r.core.lastCommitted < w.view).filter fun w =>
          !((releaseBatch c h r).any fun (held, _) => held == w) }
      ((releaseBatch c h r).foldl (fun core (_, m) => liveStep c core (.delivery m)) r.core) := rfl

theorem batch_mem (c : Config) (h : ChainDigest) (r : Replica) :
    ∀ x ∈ releaseBatch c h r, x.1 ∈ r.far ∧ decode h r x.1 = some x.2 := by
  intro x member
  have ready : ∀ x ∈ (r.far.filter fun w => r.core.lastCommitted < w.view).filterMap
      (fun w => (decode h r w).map fun m => (w, m)), x.1 ∈ r.far ∧ decode h r x.1 = some x.2 := by
    intro x inside
    obtain ⟨w, held, named⟩ := List.mem_filterMap.mp inside
    obtain ⟨m, decoded, rfl⟩ := Option.map_eq_some_iff.mp named
    exact ⟨List.mem_of_mem_filter held, decoded⟩
  unfold releaseBatch at member
  dsimp only at member
  split at member
  · exact ready x (List.mem_of_mem_filter member)
  · split at member
    · cases member
    · split at member
      · cases member
      · exact ready x (List.mem_of_mem_filter member)

theorem release_far (c : Config) (h : ChainDigest) (r : Replica) :
    ∀ x ∈ (release c h r).far, x ∈ r.far := by
  intro x member
  rw [release_shape] at member
  split at member
  · exact List.mem_of_mem_filter member
  · rw [finish_far] at member
    exact List.mem_of_mem_filter (List.mem_of_mem_filter member)

theorem fold_forget (c : Config) (batch : List (WireMessage × Message)) (G : State) :
    batch.foldl (fun core (_, m) => liveStep c core (.delivery m)) (forget G) =
      forget (batch.foldl (fun G (x : WireMessage × Message) => step c G (.delivery x.2)) G) := by
  induction batch generalizing G with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨held, m⟩ := head
    simp only [List.foldl_cons]
    rw [liveStep_forget]
    exact ih _

theorem ran_fold {c : Config} {faulty : Finset Nat} {p base : Nat} {chain : Block}
    {trail : List Event} {G : State}
    (honest : p ∉ faulty) (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults) :
    ∀ (batch : List (WireMessage × Message)) {trail1 : List Event} {G1 : State},
      Ran c faulty p base chain trail G trail1 G1 →
      (∀ x ∈ batch, x.2.kind ≠ .propose → base < x.2.view →
        (x.2.kind = .vote ∨ x.2.kind = .commit → x.2.value ≠ none) →
        (.send (liftMessage chain x.2) : Event) ∈ trail1) →
      ∃ trail2, Ran c faulty p base chain trail G trail2
        (batch.foldl (fun G (x : WireMessage × Message) => step c G (.delivery x.2)) G1) := by
  intro batch
  induction batch with
  | nil => intro trail1 G1 ran _; exact ⟨trail1, ran⟩
  | cons head rest ih =>
    intro trail1 G1 ran avail
    obtain ⟨fresh, ran2⟩ := ran_step ran honest size faultBound (.delivery head.2)
      (fun kindOK above valued => avail head (by simp) kindOK
        (Nat.lt_of_le_of_lt ran.ghost.baseLe above) valued)
    exact ih ran2 (fun x member a b d =>
      List.mem_append.mpr (Or.inl (avail x (List.mem_cons_of_mem _ member) a b d)))

/-- **Releasing what was held.** -/
theorem side_release {c : Config} {h : ChainDigest} {faulty : Finset Nat} {p base : Nat} {G : State}
    {trail : List Event} {durable chain : Block} {sent : List (Block × WireMessage)} {r : Replica}
    (side : Side c h faulty p base G trail durable chain sent r) (good : Good c faulty trail)
    (honest : p ∉ faulty) (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults)
    (covered : ∀ w ∈ r.far, ∀ m, decode h r w = some m → Covered faulty base chain trail m) :
    ∃ extra base' G', (∀ m, (.send m : Event) ∈ extra → m.sender = p ∨ m.sender ∈ faulty) ∧
      Good c faulty (trail ++ extra) ∧
      Side c h faulty p base' G' (trail ++ extra) durable
        (durable ++ (release c h r).committed) sent (release c h r) := by
  rw [release_shape]
  split
  · refine ⟨[], base, G, by simp, by rw [List.append_nil]; exact good, ?_⟩
    rw [List.append_nil, ← side.wire.pending]
    exact ⟨side.ghost, side.floor, side.tipped, side.core, side.quiet, side.wire⟩
  · obtain ⟨side0, good0, bad⟩ :=
      side_faulty side good honest ((releaseBatch c h r).map (·.2))
    obtain ⟨trail2, ran⟩ := ran_fold honest size faultBound (releaseBatch c h r)
      (ran_refl side0.ghost good0 side0.floor side0.tipped) (fun x member a b d => by
        obtain ⟨held, decoded⟩ := batch_mem c h r x member
        rcases covered x.1 held x.2 decoded a b d with inside | byz
        · exact List.mem_append.mpr (Or.inl inside)
        · exact List.mem_append.mpr (Or.inr (List.mem_map_of_mem
            (List.mem_filter.mpr ⟨List.mem_map_of_mem member, decide_eq_true byz⟩))))
    have folded : (releaseBatch c h r).foldl (fun core (_, m) => liveStep c core (.delivery m)) r.core =
        forget ((releaseBatch c h r).foldl
          (fun G (x : WireMessage × Message) => step c G (.delivery x.2)) G) := by
      rw [side.core]; exact fold_forget c _ G
    obtain ⟨extra, base', G', senders, good', side'⟩ := side_finish
      (r := { r with far := (r.far.filter fun w => r.core.lastCommitted < w.view).filter fun w =>
          !((releaseBatch c h r).any fun (held, _) => held == w) })
      ⟨side0.ghost, side0.floor, side0.tipped, side0.core, side0.quiet, side0.wire⟩
      ran honest size faultBound
    refine ⟨faultySends faulty chain ((releaseBatch c h r).map (·.2)) ++ extra, base', G', ?_, ?_, ?_⟩
    · intro m member
      rcases List.mem_append.mp member with first | second
      · exact Or.inr (bad m first)
      · exact senders m second
    · rw [← List.append_assoc]; exact good'
    · rw [← List.append_assoc, folded]; exact side'

#assert_axioms ran_step
#assert_axioms side_finish
#assert_axioms side_deliver
#assert_axioms side_release

end Minidregg.Verify.GenericSimplexRelativeSide
