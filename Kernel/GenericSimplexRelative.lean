/- The running replica of the agreement engine. Its blocks are relative: a block is the
payloads above the replica's committed height, on the wire and in memory, so nothing a
replica reads on one input grows with the committed history.

`Replica.step` is `liveStep` between a codec and a delivery policy. It is not a second
engine: every rule that acts is `GenericSimplex.step`'s.

* Codec. A `WireMessage` carries its sender's committed height and the block as the suffix
  above it. A receiver at the same or a greater height drops what it has already committed
  (`decode`); a receiver at a lower height cannot read the block and keeps nothing of it but
  the fact that the sender is ahead. After a commit the replica moves its own origin up
  (`rebase`): every block it keeps loses the committed prefix, and a received message whose
  block does not extend the commit is dropped; a dropped VOTE leaves a `tombstone`, so a
  member that voted twice in a view stays excluded from its VOTE counts.
* Delivery policy. A message the replica cannot read, or a COMMIT for a view above its
  horizon, is not handed to the engine. One held COMMIT per member waits in `far`, and the
  engine gets a held group when a quorum of members names the same view and block
  (`release`). Holding and reordering deliveries is something the specification's network
  may always do, so the policy needs no safety argument of its own. (The cap on a member's
  messages of one kind in one view is the specification's: `GenericSimplex.overCap`.)
* Recovery. A replica keeps the COMMIT evidence of its last `Config.window` commits, each
  relative to the height before that commit. A peer that asks to leave a view (CANDIDATE(⊥))
  from a lower height is owed, each time it asks, the evidence from its own height on, in
  order, if the replica still keeps the commit that starts there. A replica further behind
  reads nothing a peer keeps in memory: it needs the earlier certificates in order from a
  peer's durable record. That transfer is the driver's.

* The signed statement. A COMMIT is signed over `(view, length, digest)`: the length of the
  chain it is for and that chain's running digest (`ChainDigest`). Neither depends on the
  height the block is written from, so two members at different heights sign the same bytes
  for the same chain, and a peer can pass a COMMIT on written from any height. A replica
  keeps the digest of its committed chain, extends it over the payloads it commits, and
  reads a COMMIT only when the block it reads has the stated length and digest
  (`decode`): the cost is the block, never the chain.

Kernel-only. Proved here: the codec's transport (`above_denotes`, `decode_encode`,
`decode_ahead`), that a COMMIT a replica reads is for the chain that was signed
(`commit_reads_signed_chain`, given a collision-free digest), the rebase's
(`strip_denotes`, `strip_conflict`), one held message per member (`holdFar_unique`). Stated, not proved: `RelativeAgreement`, `RelativeFaithful`
(`Verify/GenericSimplexRelativeReach.lean`). -/
module

public import Kernel.GenericSimplex

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.Util

@[expose] public section

namespace Minidregg.Kernel.GenericSimplexRelative
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false

/-- The running digest of a chain: `origin` for the empty chain, extended one payload at a
time. Natively `origin` is cSHAKE256 of the domain's context and `extend` is cSHAKE256 of
the digest followed by the length-prefixed payload (`GenericSimplexCodec.chainDigest`). -/
structure ChainDigest where
  origin : Bytes
  extend : Bytes → Bytes → Bytes

/-- The digest of a chain that continues with `run` from a chain whose digest is `digest`. -/
def ChainDigest.over (h : ChainDigest) (digest : Bytes) (run : Block) : Bytes := run.foldl h.extend digest
def ChainDigest.of (h : ChainDigest) (chain : Block) : Bytes := h.over h.origin chain

theorem ChainDigest.over_append (h : ChainDigest) (digest : Bytes) (a b : Block) :
    h.over digest (a ++ b) = h.over (h.over digest a) b := List.foldl_append

/-- No two chains have one digest. A hash function meets this only as an assumption about
the chains that occur; it is a named premise wherever it is used. -/
def ChainDigest.CollisionFree (h : ChainDigest) : Prop := ∀ a b : Block, h.of a = h.of b → a = b

/-- A message as it travels: the sender's committed height, and the block as the payloads
above that height. A COMMIT also carries what its sender signed: the length and the
running digest of the chain it is for. -/
structure WireMessage where
  sender : Nat
  view : Nat
  kind : Kind
  height : Nat
  value : Argument
  statement : Option (Nat × Bytes) := none
  deriving DecidableEq, BEq, Repr, Inhabited

inductive WireInput where
  | delivery (message : WireMessage)
  | deliveryAt (now : Nat) (message : WireMessage)
  | tick (now : Nat)
  /-- Source records the checker has replayed, starting at application height `height`. -/
  | checked (height : Nat) (records : Block)
  | offer (payload : Bytes)
  | poll
  deriving DecidableEq, BEq, Repr, Inhabited

structure Replica where
  /-- The engine's state. Its genesis is this replica's committed chain: `committedTip` is
  empty between inputs and every block is the payloads above `height`. -/
  core : State
  /-- Payloads committed so far (the length of the committed chain). -/
  height : Nat := 0
  /-- The running digest of the committed chain. -/
  digest : Bytes
  /-- Source records committed so far (its nonempty payloads). -/
  records : Nat := 0
  /-- The COMMIT messages of the last `Config.window` commits, oldest first, each with the
  height and digest before that commit, which its blocks are relative to. The last entry is
  `core.floorEvidence`. -/
  evidence : List (Nat × Bytes × List Message) := []
  /-- At most one held COMMIT per member: unreadable yet, or for a view above the horizon. -/
  far : List WireMessage := []
  /-- Outputs since the last `drain`. -/
  sends : List WireMessage := []
  owed : List (Nat × WireMessage) := []
  committed : Block := []
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The height and digest `core.floorEvidence` is relative to: those before the floor's commit. -/
def Replica.evidenceOrigin (h : ChainDigest) (r : Replica) : Nat × Bytes :=
  (r.evidence.getLast?.map fun entry => (entry.1, entry.2.1)).getD (0, h.origin)

/-- A message written from a height whose chain has digest `digest`. The statement of a
COMMIT is a function of the chain alone, so a peer that passes one on from another height
writes the same statement. -/
def encode (h : ChainDigest) (height : Nat) (digest : Bytes) (m : Message) : WireMessage :=
  ⟨m.sender, m.view, m.kind, height, m.value,
    if m.kind == .commit then m.value.map fun run => (height + run.length, h.over digest run) else none⟩

/-- The part of a run of payloads starting at `base` that lies above `own`, when the run
starts at or below `own` and reaches strictly above it. -/
def above (base own : Nat) (run : Block) : Option Block :=
  if base ≤ own && own - base < run.length then some (run.drop (own - base)) else none

/-- What the replica reads. A COMMIT is read only if the block it reads is the one the
statement names: the stated length and digest are those of this replica's chain continued
with the block. -/
def decode (h : ChainDigest) (r : Replica) (m : WireMessage) : Option Message :=
  match m.value with
  | none => some ⟨m.sender, m.view, m.kind, none⟩
  | some run => (above m.height r.height run).bind fun block =>
      if m.kind == .commit && m.statement != some (r.height + block.length, h.over r.digest block) then none
      else some ⟨m.sender, m.view, m.kind, some block⟩

/-! ## Moving the origin after a commit -/

/-- A block that strictly extends the commit, with the commit removed. -/
def strip (tip block : Block) : Option Block :=
  if isPrefix tip block && tip.length < block.length then some (block.drop tip.length) else none

def stripArgument (tip : Block) : Argument → Option Argument
  | none => some none
  | some block => (strip tip block).map some

def stripOption (tip : Block) : Option Block → Option (Option Block)
  | none => some none
  | some block => (strip tip block).map some

/-- What is kept of a VOTE whose block does not extend the commit: that its sender voted
for something else in this view. The engine reads a view's VOTEs across values in one
place, `voteEquivocator`, and a replica that forgot the vote would start counting an
equivocator's other vote. The empty block is a value no wire message decodes to
(`decode_nonempty`), and no correct member is among its senders. -/
def tombstone (m : Message) : Message := { m with value := some [] }

/-- A view above the floor after a commit of `tip`. Received messages that do not extend
the commit are dropped (a VOTE leaves its `tombstone`): no correct member sent them. What this replica itself sent,
prepared or proposed must extend it; if not, the result is `none` and the replica halts. -/
def rebaseView (c : Config) (self : Nat) (tip : Block) (v : View) : Option View := do
  let sentCommit ← stripOption tip v.sentCommit
  let committed ← stripOption tip v.committed
  let sentCandidates ← v.sentCandidates.mapM (stripArgument tip)
  let sentReadyCore ← v.sentReadyCore.mapM (stripArgument tip)
  let sentReadyRelay ← v.sentReadyRelay.mapM (stripArgument tip)
  let prepared ← v.prepared.mapM (strip tip)
  let proposal ← match v.proposal with
    | none => some none
    | some block =>
        match strip tip block with
        | some block => some (some block)
        | none => if c.leader v.number == self then none else some none
  some { v with
    proposal, sentCommit, committed, sentCandidates, sentReadyCore, sentReadyRelay, prepared
    received := v.received.foldl (fun kept m =>
      match stripArgument tip m.value with
      | some value => kept ++ [{ m with value }]
      | none => if m.kind == .vote then addUnique kept (tombstone m) else kept) [] }

/-- After a step that committed, the committed payloads leave the engine's state: the
height rises by their number, every kept block loses them, and the floor view keeps only
the parent it offers (the empty block, which now denotes the committed chain). The floor
evidence stays as it is, relative to `evidenceHeight`. -/
def rebase (c : Config) (h : ChainDigest) (r : Replica) : Replica :=
  let core := r.core
  let tip := core.committedTip
  if tip.isEmpty then r else
  let history := applicationHistory tip
  let views := core.views.mapM fun v =>
    if v.number ≤ core.lastCommitted then
      if v.committed == some tip then
        some { number := v.number, prepared := [[]], committed := some [], disabled := v.disabled }
      else none
    else rebaseView c core.self tip v
  match views with
  | none => { r with core := { core with failed := true } }
  | some views =>
    { r with
      core := { core with views, checked := core.checked.filterMap (strip history),
                          committedTip := [], delivered := [] }
      height := r.height + tip.length, records := r.records + history.length
      digest := h.over r.digest tip
      committed := r.committed ++ tip }

/-! ## One input -/

/-- Outputs of an engine step leave in wire form, then the origin moves if it committed.
Floor evidence (a relayed message for the floor view) is relative to `evidenceOrigin`;
everything else to the height the step ran at. -/
def finish (c : Config) (h : ChainDigest) (r : Replica) (core : State) : Replica :=
  let floor := r.core.lastCommitted
  let before := r.evidenceOrigin h
  rebase c h { r with
    core := { core with outbox := [], relay := [] }
    sends := r.sends ++ core.outbox.map (encode h r.height r.digest)
    owed := r.owed ++ core.relay.map fun (peer, m) =>
      (peer, if m.view ≤ floor then encode h before.1 before.2 m else encode h r.height r.digest m)
    evidence :=
      if floor < core.lastCommitted then
        let all := r.evidence ++ [(r.height, r.digest, core.floorEvidence)]
        all.drop (all.length - c.window)
      else r.evidence }

/-- Keep one COMMIT per member for later: the one for its highest view. -/
def holdFar (far : List WireMessage) (w : WireMessage) : List WireMessage :=
  if far.any (fun old => old.sender == w.sender && w.view < old.view) then far
  else far.filter (fun old => old.sender != w.sender) ++ [w]

def deliver (c : Config) (h : ChainDigest) (r : Replica) (now : Option Nat) (w : WireMessage) : Replica :=
  if w.sender ≥ c.parties then r else
  let core := r.core
  -- A peer asking to leave from a lower height is owed every kept commit from its height on.
  let asked := w.kind == .candidate && w.value.isNone && w.sender != core.self &&
    w.height < r.height && r.evidence.any (fun entry => entry.1 == w.height)
  let answer := (r.evidence.filter fun entry => w.height ≤ entry.1).flatMap fun entry =>
    entry.2.2.map fun m => (w.sender, encode h entry.1 entry.2.1 m)
  let r := if asked then { r with owed := r.owed ++ answer } else r
  match decode h r w with
  | none =>
      if r.height < w.height then
        -- The sender has committed more than this replica: all it keeps is that fact, and a COMMIT.
        let core := noteAhead core w.sender (max w.view (core.current + 1))
        finish c h { r with far := if w.kind == .commit then holdFar r.far w else r.far } core
      else finish c h r core
  | some m =>
      if m.kind == .commit && horizon c core < m.view then
        finish c h { r with far := holdFar r.far w } (noteAhead core m.sender m.view)
      else finish c h r (liveStep c core (match now with
        | some time => .deliveryAt time m
        | none => .delivery m))

/-- Hand the engine what was held and can now be used: every held COMMIT that is readable
and within the horizon; otherwise, unless a record above the horizon is already waiting, a
group of readable ones from a quorum of members for one view and block. -/
def release (c : Config) (h : ChainDigest) (r : Replica) : Replica :=
  let far := r.far.filter fun w => r.core.lastCommitted < w.view
  let r := { r with far }
  let ready := far.filterMap fun w => (decode h r w).map fun m => (w, m)
  let edge := horizon c r.core
  let near := ready.filter fun (_, m) => m.view ≤ edge
  let batch :=
    if !near.isEmpty then near
    else if r.core.views.any (fun v => edge < v.number) then []
    else match ready.find? (fun (_, m) =>
        (ready.filter fun (_, x) => x.view == m.view && x.value == m.value).length ≥ c.quorum) with
      | none => []
      | some (_, m) => ready.filter fun (_, x) => x.view == m.view && x.value == m.value
  if batch.isEmpty then r else
  finish c h { r with far := far.filter fun w => !(batch.any fun (held, _) => held == w) }
    (batch.foldl (fun core (_, m) => liveStep c core (.delivery m)) r.core)

def Replica.step (c : Config) (h : ChainDigest) (r : Replica) (input : WireInput) : Replica :=
  release c h (match input with
    | .delivery w => deliver c h r none w
    | .deliveryAt now w => deliver c h r (some now) w
    | .tick now => finish c h r (liveStep c r.core (.tick now))
    | .checked height records =>
        match above height r.records records with
        | some run => finish c h r (liveStep c r.core (.checked run))
        | none => r
    | .offer payload => finish c h r (liveStep c r.core (.offer payload))
    | .poll => finish c h r (liveStep c r.core .poll))

def Replica.start (c : Config) (h : ChainDigest) (self now : Nat) : Replica :=
  let core := forget (GenericSimplex.start c self now)
  finish c h { core := core, digest := h.origin } core

structure Output where
  sends : List WireMessage
  owed : List (Nat × WireMessage)
  committed : Block

def Replica.drain (r : Replica) : Output × Replica :=
  (⟨r.sends, r.owed, r.committed⟩, { r with sends := [], owed := [], committed := [] })

/-! ## The codec's transport

`chain ++ block` is the whole chain a replica's block denotes, `chain` being what it has
committed. These are the facts that make a wire message mean the same chain at its sender
and at a receiver. -/

/-- A receiver whose committed chain is a strict prefix of the chain the sender meant reads
that same chain. `sender` and `receiver` are the two committed chains. -/
theorem above_denotes (sender receiver run : Block)
    (extends_ : receiver <+: sender ++ run) (strictly : receiver.length < (sender ++ run).length)
    (behind : sender.length ≤ receiver.length) :
    ∃ block, above sender.length receiver.length run = some block ∧
      receiver ++ block = sender ++ run := by
  obtain ⟨rest, whole⟩ := extends_
  have short : receiver.length - sender.length < run.length := by
    rw [List.length_append] at strictly; omega
  refine ⟨run.drop (receiver.length - sender.length), ?_, ?_⟩
  · unfold above
    simp [behind, short]
  · have cut : receiver = sender ++ run.take (receiver.length - sender.length) := by
      have taken := congrArg (List.take receiver.length) whole
      rw [List.take_left, List.take_append, List.take_of_length_le behind] at taken
      exact taken
    calc receiver ++ run.drop (receiver.length - sender.length)
        = (sender ++ run.take (receiver.length - sender.length)) ++
            run.drop (receiver.length - sender.length) := by rw [← cut]
      _ = sender ++ run := by rw [List.append_assoc, List.take_append_drop]

/-- At the sender's own height the block is read back unchanged. -/
theorem decode_encode (h : ChainDigest) (r : Replica) (m : Message)
    (nonempty : ∀ block, m.value = some block → block ≠ []) :
    decode h r (encode h r.height r.digest m) = some m := by
  cases m with
  | mk sender view kind value =>
    cases value with
    | none => rfl
    | some block =>
      have positive : 0 < block.length := List.length_pos_iff.mpr (nonempty block rfl)
      by_cases commit : kind = .commit <;> simp [decode, encode, above, positive, commit]

/-- What `decode` yields for a block: the payloads above the replica's height, and for a
COMMIT the statement checked against them. -/
theorem decode_some (h : ChainDigest) (r : Replica) (w : WireMessage) (m : Message) (run : Block)
    (valued : w.value = some run) (decoded : decode h r w = some m) :
    w.height ≤ r.height ∧ r.height - w.height < run.length ∧
      m = ⟨w.sender, w.view, w.kind, some (run.drop (r.height - w.height))⟩ ∧
      (w.kind = .commit → w.statement = some (r.height + (run.drop (r.height - w.height)).length,
        h.over r.digest (run.drop (r.height - w.height)))) := by
  simp only [decode, valued, above] at decoded
  by_cases holds : (decide (w.height ≤ r.height) && decide (r.height - w.height < run.length)) = true
  · simp only [holds, if_true, Option.bind_some] at decoded
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at holds
    split at decoded
    · cases decoded
    · rename_i checked
      simp only [Option.some.injEq] at decoded
      refine ⟨holds.1, holds.2, decoded.symm, ?_⟩
      intro commit
      simpa [commit] using checked
  · simp [holds] at decoded

/-- No wire message decodes to the empty block: it is free to mark a `tombstone`. -/
theorem decode_nonempty (h : ChainDigest) (r : Replica) (w : WireMessage) (m : Message) (block : Block)
    (decoded : decode h r w = some m) (valued : m.value = some block) : block ≠ [] := by
  cases value : w.value with
  | none =>
    simp only [decode, value, Option.some.injEq] at decoded
    rw [← decoded] at valued
    cases valued
  | some run =>
    obtain ⟨_, short, same, _⟩ := decode_some h r w m run value decoded
    rw [same] at valued
    simp only [Option.some.injEq] at valued
    intro empty
    rw [← valued] at empty
    have := congrArg List.length empty
    rw [List.length_drop, List.length_nil] at this
    omega

/-- A block from a sender that has committed more is not read. -/
theorem decode_ahead (h : ChainDigest) (r : Replica) (w : WireMessage) (run : Block)
    (valued : w.value = some run) (ahead : r.height < w.height) : decode h r w = none := by
  unfold decode above
  rw [valued]
  have no : (decide (w.height ≤ r.height) && decide (r.height - w.height < run.length)) = false := by
    rw [Bool.and_eq_false_iff]; left; rw [decide_eq_false_iff_not]; omega
  simp only [no, Bool.false_eq_true, ite_false, Option.bind_none]

/-- **A COMMIT that is read is for the chain that was signed.** `chain` is what the replica
has committed and `signed` the chain the statement was made for, at whatever height its
block was written from, by its sender or by a peer passing it on. -/
theorem commit_reads_signed_chain (h : ChainDigest) (free : h.CollisionFree) (r : Replica)
    (chain signed block : Block) (w : WireMessage) (m : Message)
    (tracks : r.digest = h.of chain) (commit : w.kind = .commit)
    (statement : w.statement = some (signed.length, h.of signed))
    (decoded : decode h r w = some m) (valued : m.value = some block) : chain ++ block = signed := by
  cases value : w.value with
  | none =>
    simp only [decode, value, Option.some.injEq] at decoded
    rw [← decoded] at valued
    cases valued
  | some run =>
    obtain ⟨_, _, same, checked⟩ := decode_some h r w m run value decoded
    rw [same] at valued
    simp only [Option.some.injEq] at valued
    have stated := checked commit
    rw [statement, valued, tracks] at stated
    simp only [Option.some.injEq, Prod.mk.injEq] at stated
    apply free
    rw [ChainDigest.of, ChainDigest.over_append]
    exact stated.2.symm

/-- Moving the origin keeps what a block denotes. -/
theorem strip_denotes (chain tip block rest : Block) (kept : strip tip block = some rest) :
    (chain ++ tip) ++ rest = chain ++ block ∧ rest ≠ [] := by
  unfold strip at kept
  split at kept
  · rename_i holds
    rw [Bool.and_eq_true, decide_eq_true_eq] at holds
    obtain ⟨starts, longer⟩ := holds
    have same : block.take tip.length = tip := by
      unfold isPrefix at starts; exact beq_iff_eq.mp starts
    cases kept
    constructor
    · rw [List.append_assoc]
      conv => lhs; arg 2; arg 1; rw [← same]
      rw [List.take_append_drop]
    · intro empty
      have := congrArg List.length empty
      rw [List.length_drop, List.length_nil] at this
      omega
  · cases kept

/-- A block that does not extend the commit, or is the commit, is not kept. -/
theorem strip_conflict (tip block : Block) (conflict : ¬ (tip <+: block ∧ tip ≠ block)) :
    strip tip block = none := by
  unfold strip
  split
  · rename_i holds
    rw [Bool.and_eq_true, decide_eq_true_eq] at holds
    obtain ⟨starts, longer⟩ := holds
    exfalso
    apply conflict
    constructor
    · unfold isPrefix at starts
      rw [beq_iff_eq] at starts
      exact List.prefix_iff_eq_take.mpr starts.symm
    · intro same; rw [same] at longer; omega
  · rfl

def FarUnique (far : List WireMessage) : Prop := (far.map WireMessage.sender).Nodup

/-- `far` holds one message per member, so at most `parties` of them. -/
theorem holdFar_unique (far : List WireMessage) (w : WireMessage) (old : FarUnique far) :
    FarUnique (holdFar far w) := by
  unfold holdFar
  split
  · exact old
  · unfold FarUnique at old ⊢
    rw [List.map_append, List.nodup_append]
    refine ⟨(old.sublist (List.Sublist.map _ List.filter_sublist)), by simp, ?_⟩
    intro a inKept b inNew
    rw [List.map_singleton, List.mem_singleton] at inNew
    obtain ⟨kept, member, named⟩ := List.mem_map.mp inKept
    have other := (List.mem_filter.mp member).2
    rw [bne_iff_ne] at other
    rw [inNew, ← named]
    exact other

end Minidregg.Kernel.GenericSimplexRelative
