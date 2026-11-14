import Verify.GenericSimplexRelativeSide

/-! The induction over a run of running replicas.

`Tracked net trail`: `trail` is a trace of the abstract model (`Good`), every correct
replica of `net` has its side of it (`Side`, drained), and every COMMIT a correct replica
holds was delivered to it and is authentic.

* `faithful_of_tracked`: a tracked network has the trace `RelativeFaithful` asks for.
* `read_covered` (the reading lemma): what a replica decodes from an authentic message, and
  `ingest` can record, is a SEND of the trail at the reader's chain. A correct member's
  block above the reader's committed view extends the reader's chain
  (`support_extends_commit`); a COMMIT is the signed chain when the digest has no collision
  among the chains that occur (`commit_reads_signed_chain`).
* `tracked_advance`: one input of a run keeps a network tracked.
* `relative_faithful`: `RelativeFaithful` holds if the initial network is tracked
  (`TrackedInitial`, stated). -/
namespace Minidregg.Verify.GenericSimplexRelativeFaithful
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexRelative
open Minidregg.Kernel.GenericSimplexLocal
open Minidregg.Kernel.GenericSimplexPreparedHistory
open Minidregg.Kernel.GenericSimplexTrail
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GenericSimplexSupportExtends
open Minidregg.Verify.GenericSimplexRelativeReach
open Minidregg.Verify.GenericSimplexRelativeSide
set_option autoImplicit false

structure Tracked (c : Config) (h : ChainDigest) (faulty : Finset Nat) (net : RelNetwork)
    (trail : List Event) : Prop where
  good : Good c faulty trail
  sides : ∀ p, p < c.parties → p ∉ faulty → ∃ base G,
    Side c h faulty p base G trail (net.chain p) (net.chain p) (net.sent p) (net.replica p) ∧
      (net.replica p).sends = []
  far : ∀ p, p < c.parties → p ∉ faulty → ∀ w ∈ (net.replica p).far,
    w ∈ net.seen p ∧ w.kind = .commit ∧ RelAuthentic c faulty net w

/-- **A tracked network has its own trace of the model.** -/
theorem faithful_of_tracked {c : Config} {h : ChainDigest} {faulty : Finset Nat} {net : RelNetwork}
    {trail : List Event} (tracked : Tracked c h faulty net trail)
    (size : c.parties = 3 * c.faults + 1) : Faithful c faulty net (localTrace trail) := by
  refine ⟨good_faithful tracked.good size, ?_, ?_, ?_⟩
  · intro p pm ph
    obtain ⟨base, G, side, _⟩ := tracked.sides p pm ph
    exact ⟨base, side.ghost.committed⟩
  · intro p pm ph entry member own
    obtain ⟨base, G, side, _⟩ := tracked.sides p pm ph
    exact member_trace (side.wire.sent entry member own).2.1
  · intro t m output mm mh
    obtain ⟨base, G, side, drained⟩ := tracked.sides m.sender mm mh
    rcases side.wire.only m (trace_member (by simp) output) rfl with durableOne | ⟨w, queued, _⟩
    · exact durableOne
    · rw [drained] at queued; cases queued

/-! ## The reading lemma -/

theorem decode_head {h : ChainDigest} {r : Replica} {w : WireMessage} {m : Message}
    (decoded : decode h r w = some m) : m.sender = w.sender ∧ m.view = w.view ∧ m.kind = w.kind := by
  cases value : w.value with
  | none =>
    simp only [decode, value, Option.some.injEq] at decoded
    rw [← decoded]
    exact ⟨rfl, rfl, rfl⟩
  | some run =>
    obtain ⟨_, _, same, _⟩ := decode_some h r w m run value decoded
    rw [same]
    exact ⟨rfl, rfl, rfl⟩

theorem reads_of_decode {h : ChainDigest} {r : Replica} {w : WireMessage} {m : Message}
    {chain block : Block} (decoded : decode h r w = some m) (commit : w.kind = .commit)
    (valued : m.value = some block) (height : r.height = chain.length) (digest : r.digest = h.of chain) :
    Reads h chain w (chain ++ block) := by
  cases wv : w.value with
  | none =>
    simp only [decode, wv, Option.some.injEq] at decoded
    rw [← decoded] at valued
    cases valued
  | some run =>
    obtain ⟨behind, short, same, checked⟩ := decode_some h r w m run wv decoded
    rw [same] at valued
    simp only [Option.some.injEq] at valued
    refine ⟨run, block, wv, ?_, rfl, ?_⟩
    · unfold above
      rw [← height]
      simp [behind, short, valued]
    · rw [checked commit, valued, height, digest, List.length_append, ChainDigest.of, ChainDigest.of,
        ChainDigest.over_append]

/-- **The reading lemma.** `entry` is what the sender wrote, if it is correct. -/
theorem read_covered {c : Config} {h : ChainDigest} {faulty : Finset Nat} {occurs : Block → Prop}
    (free : h.CollisionFreeOn occurs) {trail : List Event} (good : Good c faulty trail)
    (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults)
    {base : Nat} {chain : Block} {r : Replica}
    (committed : CommittedAt (localTrace trail) faulty base chain)
    (height : r.height = chain.length) (digest : r.digest = h.of chain)
    {w : WireMessage} {m : Message} (decoded : decode h r w = some m)
    (authentic : w.sender ∈ faulty ∨ ∃ entry : Block × WireMessage, Own h trail entry.1 entry.2 ∧
      (∀ whole, entry.2.kind = .commit → (denote entry.1 entry.2).value = some whole → occurs whole) ∧
      if w.kind = .commit then
        entry.2.sender = w.sender ∧ entry.2.kind = .commit ∧ entry.2.view = w.view ∧
          entry.2.statement = w.statement
      else entry.2 = w)
    (read : w.kind = .commit → ∀ block, m.value = some block → occurs (chain ++ block)) :
    Covered faulty base chain trail m := by
  intro kindOK above valued
  obtain ⟨sender, view, kind⟩ := decode_head decoded
  by_cases byz : w.sender ∈ faulty
  · exact Or.inr (sender ▸ byz)
  rcases authentic with bad | ⟨entry, own, signed, rel⟩
  · exact absurd bad byz
  left
  have rules := good_faithful good size
  have roster : (Finset.range c.parties).card = 3 * c.faults + 1 := by simpa using size
  by_cases commit : w.kind = .commit
  · rw [if_pos commit] at rel
    obtain ⟨eSender, eKind, eView, eStatement⟩ := rel
    have mCommit : m.kind = .commit := kind.trans commit
    cases value : m.value with
    | none => exact absurd value (valued (Or.inr mCommit))
    | some block =>
      cases wv : w.value with
      | none =>
        simp only [decode, wv, Option.some.injEq] at decoded
        rw [← decoded] at value
        cases value
      | some run =>
        obtain ⟨_, _, _, checked⟩ := decode_some h r w m run wv decoded
        have ownStated := own.2.2 eKind
        rw [eStatement, checked commit] at ownStated
        cases dv : (denote entry.1 entry.2).value with
        | none => rw [dv] at ownStated; cases ownStated
        | some whole =>
          rw [dv] at ownStated
          have wStatement : w.statement = some (whole.length, h.of whole) := by
            rw [checked commit]; exact ownStated
          have same := commit_reads_signed_chain h occurs free r chain whole block w m digest commit
            wStatement decoded value (read commit block value) (signed whole eKind dv)
          have named : liftMessage chain m = denote entry.1 entry.2 := by
            have lifted : liftMessage chain m = ⟨m.sender, m.view, m.kind, some (chain ++ block)⟩ := by
              unfold liftMessage liftArgument; rw [value]; rfl
            have d : denote entry.1 entry.2 =
                ⟨entry.2.sender, entry.2.view, entry.2.kind, (denote entry.1 entry.2).value⟩ := rfl
            rw [lifted, sender, view, mCommit, same, d, dv, eSender, eView, eKind]
          rw [named]
          exact own.2.1
  · rw [if_neg commit] at rel
    obtain ⟨e1, e2⟩ := entry
    dsimp only at rel own
    subst rel
    cases wv : e2.value with
    | none =>
      simp only [decode, wv, Option.some.injEq] at decoded
      have named : liftMessage chain m = denote e1 e2 := by
        rw [← decoded]; unfold liftMessage liftArgument denote; rw [wv]; rfl
      rw [named]
      exact own.2.1
    | some run =>
      obtain ⟨behind, short, same, _⟩ := decode_some h r e2 m run wv decoded
      have sentX : (.send ⟨e2.sender, e2.view, e2.kind, some (e1.take e2.height ++ run)⟩ : Event) ∈ trail := by
        have s := own.2.1
        unfold denote at s
        rw [wv] at s
        exact s
      obtain ⟨time, output⟩ := member_trace sentX
      have ext := support_extends_commit rules roster faultBound committed
        (by rw [← view]; exact above) byz (kind ▸ kindOK) output
      have lenS : (e1.take e2.height).length = e2.height := by
        rw [List.length_take]; exact Nat.min_eq_left own.1
      have cut : chain = e1.take e2.height ++ run.take (r.height - e2.height) := by
        have t := List.prefix_iff_eq_take.mp ext.1
        rw [List.take_append, lenS, List.take_of_length_le (by rw [lenS, ← height]; exact behind),
          ← height] at t
        exact t
      have named : liftMessage chain m = ⟨e2.sender, e2.view, e2.kind, some (e1.take e2.height ++ run)⟩ := by
        rw [same]
        show (⟨e2.sender, e2.view, e2.kind, some (chain ++ run.drop (r.height - e2.height))⟩ : Message) = _
        conv_lhs => rw [cut]
        rw [List.append_assoc, List.take_append_drop]
      rw [named]
      exact sentX

/-! ## One input of a run -/

theorem sent_grows (c : Config) (h : ChainDigest) (net : RelNetwork) (party : Nat) (input : WireInput)
    (q : Nat) : ∀ entry ∈ net.sent q, entry ∈ (relAdvance c h net party input).sent q := by
  intro entry member
  show entry ∈ (if q = party then _ else _)
  split
  · rename_i same; subst same; exact List.mem_append.mpr (Or.inl member)
  · exact member

theorem seen_grows (c : Config) (h : ChainDigest) (net : RelNetwork) (party : Nat) (input : WireInput)
    (q : Nat) : ∀ w ∈ net.seen q, w ∈ (relAdvance c h net party input).seen q := by
  intro w member
  show w ∈ (if q = party then _ else _)
  split
  · rename_i same; subst same; exact List.mem_append.mpr (Or.inl member)
  · exact member

theorem chain_grows (c : Config) (h : ChainDigest) (net : RelNetwork) (party : Nat) (input : WireInput)
    (q : Nat) : net.chain q <+: (relAdvance c h net party input).chain q := by
  show _ <+: (if q = party then _ else _)
  split
  · rename_i same; subst same; exact List.prefix_append _ _
  · exact List.prefix_refl _

/-- The chains that occur only grow along a run. -/
theorem occurs_mono {c : Config} {h : ChainDigest} {faulty : Finset Nat} {net : RelNetwork}
    (party : Nat) (input : WireInput) {chain : Block} (occurs : Occurs c h faulty net chain) :
    Occurs c h faulty (relAdvance c h net party input) chain := by
  rcases occurs with ⟨p, pm, ph, entry, member, rest⟩ | ⟨p, pm, ph, w, member, held, isPre, reads⟩
  · exact Or.inl ⟨p, pm, ph, entry, sent_grows c h net party input p entry member, rest⟩
  · exact Or.inr ⟨p, pm, ph, w, seen_grows c h net party input p w member, held,
      isPre.trans (chain_grows c h net party input p), reads⟩

/-- The replica after its input, before it releases what it holds. -/
def handled (c : Config) (h : ChainDigest) (r : Replica) : WireInput → Replica
  | .delivery w => deliver c h r none w
  | .deliveryAt now w => deliver c h r (some now) w
  | .tick now => finish c h r (liveStep c r.core (.tick now))
  | .checked height records =>
      match above height r.records records with
      | some run => finish c h r (liveStep c r.core (.checked run))
      | none => r
  | .offer payload => finish c h r (liveStep c r.core (.offer payload))
  | .poll => finish c h r (liveStep c r.core .poll)

theorem step_shape (c : Config) (h : ChainDigest) (r : Replica) (input : WireInput) :
    r.step c h input = release c h (handled c h r input) := by
  cases input <;> rfl

theorem side_handled {c : Config} {h : ChainDigest} {faulty : Finset Nat} {p base : Nat} {G : State}
    {trail : List Event} {durable chain : Block} {sent : List (Block × WireMessage)} {r : Replica}
    (side : Side c h faulty p base G trail durable chain sent r) (good : Good c faulty trail)
    (honest : p ∉ faulty) (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults)
    (input : WireInput)
    (covered : ∀ w, (input = .delivery w ∨ ∃ now, input = .deliveryAt now w) →
      ∀ m, decode h r w = some m → Covered faulty base chain trail m) :
    ∃ extra base' G', (∀ m, (.send m : Event) ∈ extra → m.sender = p ∨ m.sender ∈ faulty) ∧
      Good c faulty (trail ++ extra) ∧
      Side c h faulty p base' G' (trail ++ extra) durable
        (durable ++ (handled c h r input).committed) sent (handled c h r input) := by
  have none : ∀ {input : Input} (m : Message), (∀ x, input ≠ .delivery x) →
      (∀ now x, input ≠ .deliveryAt now x) →
      (input = .delivery m ∨ ∃ now, input = .deliveryAt now m) → Covered faulty base chain trail m :=
    fun m a b named => by
      rcases named with same | ⟨now, same⟩
      · exact absurd same (a m)
      · exact absurd same (b now m)
  cases input with
  | delivery w =>
    unfold handled
    exact side_deliver side good honest size faultBound _ w (covered w (Or.inl rfl))
  | deliveryAt now w =>
    unfold handled
    exact side_deliver side good honest size faultBound _ w (covered w (Or.inr ⟨now, rfl⟩))
  | tick now =>
    unfold handled
    exact side_live side good honest size faultBound (.tick now)
      (fun m => none m (fun _ => by simp) (fun _ _ => by simp))
  | offer payload =>
    unfold handled
    exact side_live side good honest size faultBound (.offer payload)
      (fun m => none m (fun _ => by simp) (fun _ _ => by simp))
  | poll =>
    unfold handled
    exact side_live side good honest size faultBound .poll
      (fun m => none m (fun _ => by simp) (fun _ _ => by simp))
  | checked height records =>
    simp only [handled]
    split
    · exact side_live side good honest size faultBound (.checked _)
        (fun m => none m (fun _ => by simp) (fun _ _ => by simp))
    · refine ⟨[], base, G, by simp, by rw [List.append_nil]; exact good, ?_⟩
      rw [List.append_nil, ← side.wire.pending]
      exact side

theorem handled_far (c : Config) (h : ChainDigest) (r : Replica) (input : WireInput) :
    ∀ x ∈ (handled c h r input).far, x ∈ r.far ∨
      ((input = .delivery x ∨ ∃ now, input = .deliveryAt now x) ∧ x.kind = .commit) := by
  intro x member
  cases input with
  | delivery w =>
    unfold handled at member
    rcases deliver_far c h r _ w x member with old | ⟨rfl, commit⟩
    · exact Or.inl old
    · exact Or.inr ⟨Or.inl rfl, commit⟩
  | deliveryAt now w =>
    unfold handled at member
    rcases deliver_far c h r _ w x member with old | ⟨rfl, commit⟩
    · exact Or.inl old
    · exact Or.inr ⟨Or.inr ⟨now, rfl⟩, commit⟩
  | tick now =>
    unfold handled at member
    rw [finish_far] at member
    exact Or.inl member
  | offer payload =>
    unfold handled at member
    rw [finish_far] at member
    exact Or.inl member
  | poll =>
    unfold handled at member
    rw [finish_far] at member
    exact Or.inl member
  | checked height records =>
    simp only [handled] at member
    split at member
    · rw [finish_far] at member
      exact Or.inl member
    · exact Or.inl member

theorem release_committed (c : Config) (h : ChainDigest) (r : Replica) :
    ∃ more, (release c h r).committed = r.committed ++ more := by
  rw [release_shape]
  split
  · exact ⟨[], (List.append_nil _).symm⟩
  · rw [finish_eq, rebase_shape]
    split
    · exact ⟨[], (List.append_nil _).symm⟩
    · split
      · exact ⟨[], (List.append_nil _).symm⟩
      · exact ⟨_, rfl⟩

/-- Draining the replica: what was queued is now the durable record. -/
theorem side_drain {c : Config} {h : ChainDigest} {faulty : Finset Nat} {p base : Nat} {G : State}
    {trail : List Event} {durable chain : Block} {sent : List (Block × WireMessage)} {r : Replica}
    (side : Side c h faulty p base G trail durable chain sent r) :
    Side c h faulty p base G trail chain chain
      (sent ++ (r.sends ++ (r.owed.map (·.2)).filter (·.sender == p)).map fun m => (chain, m))
      r.drain.2 := by
  have wire := side.wire
  refine ⟨side.ghost, side.floor, side.tipped, side.core, side.quiet, ?_⟩
  refine ⟨(List.append_nil _).symm, wire.height, wire.digest, ?_, ?_, ?_, ?_, wire.evidence, wire.origin⟩
  · intro entry member own
    rcases List.mem_append.mp member with old | new
    · exact wire.sent entry old own
    · obtain ⟨w, inside, rfl⟩ := List.mem_map.mp new
      rcases List.mem_append.mp inside with queued | relayed
      · exact wire.sends w queued own
      · obtain ⟨x, held, rfl⟩ := List.mem_map.mp (List.mem_of_mem_filter relayed)
        exact wire.owed x held own
  · intro w member; cases member
  · intro x member; cases member
  · intro m member own
    rcases wire.only m member own with durableOne | ⟨w, queued, same⟩
    · obtain ⟨entry, inside, named⟩ := durableOne
      exact Or.inl ⟨entry, List.mem_append.mpr (Or.inl inside), named⟩
    · exact Or.inl ⟨(chain, w), List.mem_append.mpr (Or.inr (List.mem_map_of_mem
        (List.mem_append.mpr (Or.inl queued)))), same⟩

/-- **One input of a run keeps the network tracked.** -/
theorem tracked_advance {c : Config} {h : ChainDigest} {faulty : Finset Nat}
    {checked : Nat → Block → Prop} {net : RelNetwork} {trail : List Event} {party : Nat}
    {input : WireInput} (tracked : Tracked c h faulty net trail)
    (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults)
    (free : h.CollisionFreeOn (Occurs c h faulty (relAdvance c h net party input)))
    (allowed : RelAllowed c faulty checked net party input) :
    ∃ trail', Tracked c h faulty (relAdvance c h net party input) trail' := by
  obtain ⟨pm, ph, rest⟩ := allowed
  obtain ⟨base, G, side, _⟩ := tracked.sides party pm ph
  have sentGrows := sent_grows c h net party input
  have seenGrows := seen_grows c h net party input
  have authGrows : ∀ w, RelAuthentic c faulty net w →
      RelAuthentic c faulty (relAdvance c h net party input) w :=
    fun w ⟨wm, either⟩ => ⟨wm, either.imp id
      (fun ⟨entry, member, rel⟩ => ⟨entry, sentGrows _ entry member, rel⟩)⟩
  have fReplica : (relAdvance c h net party input).replica party =
      (release c h (handled c h (net.replica party) input)).drain.2 := by
    show (if party = party then _ else _) = _
    rw [if_pos rfl, step_shape]
  have fChain : (relAdvance c h net party input).chain party =
      net.chain party ++ (release c h (handled c h (net.replica party) input)).committed := by
    show (if party = party then _ else _) = _
    rw [if_pos rfl, step_shape]; rfl
  have fSent : (relAdvance c h net party input).sent party = net.sent party ++
      ((release c h (handled c h (net.replica party) input)).sends ++
        ((release c h (handled c h (net.replica party) input)).owed.map (·.2)).filter
          (·.sender == party)).map
        fun m => (net.chain party ++ (release c h (handled c h (net.replica party) input)).committed, m) := by
    show (if party = party then _ else _) = _
    rw [if_pos rfl, step_shape]; rfl
  have seenIn : ∀ w, (input = .delivery w ∨ ∃ now, input = .deliveryAt now w) → w.kind = .commit →
      w ∈ (relAdvance c h net party input).seen party := by
    intro w named commit
    show w ∈ (if party = party then _ else _)
    rw [if_pos rfl]
    rcases named with rfl | ⟨now, rfl⟩ <;> simp [commit]
  have auth : ∀ w, (input = .delivery w ∨ ∃ now, input = .deliveryAt now w) →
      RelAuthentic c faulty net w := by
    intro w named
    rcases named with rfl | ⟨now, rfl⟩ <;> exact rest
  -- what a correct replica decodes from an authentic message is covered
  have cover : ∀ {trail' : List Event}, Good c faulty trail' → (∀ e ∈ trail, e ∈ trail') →
      ∀ {base' : Nat} {chain' : Block} {r : Replica},
      CommittedAt (localTrace trail') faulty base' chain' → r.height = chain'.length →
      r.digest = h.of chain' → chain' <+: (relAdvance c h net party input).chain party →
      ∀ {w : WireMessage} {m : Message}, RelAuthentic c faulty net w →
      (w.kind = .commit → w ∈ (relAdvance c h net party input).seen party) →
      decode h r w = some m → Covered faulty base' chain' trail' m := by
    intro trail' good' grows base' chain' r committed height digest held w m authentic seen decoded
    refine read_covered free good' size faultBound committed height digest decoded ?_
      (fun commit block value => Or.inr ⟨party, pm, ph, w, seen commit, chain', held,
        reads_of_decode decoded commit value height digest⟩)
    obtain ⟨wm, bad | ⟨entry, member, rel⟩⟩ := authentic
    · exact Or.inl bad
    · by_cases byz : w.sender ∈ faulty
      · exact Or.inl byz
      · have eSender : entry.2.sender = w.sender := by
          split at rel
          · exact rel.1
          · rw [rel]
        obtain ⟨bq, Gq, sideq, _⟩ := tracked.sides w.sender wm byz
        exact Or.inr ⟨entry, own_trail (sideq.wire.sent entry member eSender) grows,
          fun whole eKind dv => Or.inl ⟨w.sender, wm, byz, entry, sentGrows _ entry member, eSender,
            eKind, dv⟩, rel⟩
  obtain ⟨more, grown⟩ := release_committed c h (handled c h (net.replica party) input)
  obtain ⟨extra1, base1, G1, senders1, good1, side1⟩ :=
    side_handled side tracked.good ph size faultBound input (fun w named m decoded =>
      cover tracked.good (fun _ e => e) side.ghost.committed side.wire.height side.wire.digest
        (by rw [fChain]; exact List.prefix_append _ _) (auth w named) (seenIn w named) decoded)
  have far1 := handled_far c h (net.replica party) input
  have heldOK : ∀ w ∈ (handled c h (net.replica party) input).far,
      w ∈ (relAdvance c h net party input).seen party ∧ w.kind = .commit ∧ RelAuthentic c faulty net w := by
    intro w inFar
    rcases far1 w inFar with old | ⟨named, commit⟩
    · obtain ⟨inSeen, commit, a⟩ := tracked.far party pm ph w old
      exact ⟨seenGrows _ w inSeen, commit, a⟩
    · exact ⟨seenIn w named commit, commit, auth w named⟩
  obtain ⟨extra2, base2, G2, senders2, good2, side2⟩ :=
    side_release side1 good1 ph size faultBound (fun w inFar m decoded =>
      cover good1 (fun _ e => List.mem_append.mpr (Or.inl e)) side1.ghost.committed
        side1.wire.height side1.wire.digest
        (by rw [fChain, grown, ← List.append_assoc]; exact List.prefix_append _ _)
        (heldOK w inFar).2.2 (fun _ => (heldOK w inFar).1) decoded)
  have foreign : ∀ q, q ≠ party → q ∉ faulty → ∀ (extra : List Event),
      (∀ m, (.send m : Event) ∈ extra → m.sender = party ∨ m.sender ∈ faulty) →
      ∀ m, (.send m : Event) ∈ extra → m.sender ≠ q := by
    intro q other qh extra senders m member own
    rcases senders m member with same | byz
    · exact other (own.symm.trans same)
    · exact qh (own ▸ byz)
  refine ⟨(trail ++ extra1) ++ extra2, good2, ?_, ?_⟩
  · intro q qm qh
    by_cases same : q = party
    · subst same
      refine ⟨base2, G2, ?_, ?_⟩
      · rw [fReplica, fChain, fSent]; exact side_drain side2
      · rw [fReplica]; rfl
    · obtain ⟨bq, Gq, sideq, drainedq⟩ := tracked.sides q qm qh
      have r' : (relAdvance c h net party input).replica q = net.replica q := by
        show (if q = party then _ else _) = _; rw [if_neg same]
      have c' : (relAdvance c h net party input).chain q = net.chain q := by
        show (if q = party then _ else _) = _; rw [if_neg same]
      have s' : (relAdvance c h net party input).sent q = net.sent q := by
        show (if q = party then _ else _) = _; rw [if_neg same]
      rw [r', c', s']
      exact ⟨bq, Gq, side_extend (side_extend sideq extra1 (foreign q same qh extra1 senders1)) extra2
        (foreign q same qh extra2 senders2), drainedq⟩
  · intro q qm qh w member
    by_cases same : q = party
    · subst same
      rw [fReplica] at member
      have inside : w ∈ (handled c h (net.replica q) input).far :=
        release_far c h _ w member
      obtain ⟨inSeen, commit, a⟩ := heldOK w inside
      exact ⟨inSeen, commit, authGrows w a⟩
    · have r' : (relAdvance c h net party input).replica q = net.replica q := by
        show (if q = party then _ else _) = _; rw [if_neg same]
      rw [r'] at member
      obtain ⟨inSeen, commit, a⟩ := tracked.far q qm qh w member
      exact ⟨seenGrows q w inSeen, commit, authGrows w a⟩

/-- STATEMENT (no proof): the initial network is tracked. Its trail is the correct members'
start audits, one after another; each member's side is `ghost_start` and its start's outputs.
It needs, of `GenericSimplex.start`, that nothing is committed and nothing is owed. -/
def TrackedInitial : Prop :=
  ∀ (c : Config) (h : ChainDigest) (faulty : Finset Nat) (time : Nat),
    c.parties = 3 * c.faults + 1 → faulty.card ≤ c.faults →
    ∃ trail, Tracked c h faulty (relInitial c h time) trail

/-- **`RelativeFaithful`, from the initial network.** Every reachable network of running
replicas is tracked, by induction on the run. -/
theorem relative_faithful (initial : TrackedInitial) : RelativeFaithful := by
  intro c h faulty checked time net reachable free size faultBound
  have tracked : ∃ trail, Tracked c h faulty net trail := by
    revert free
    induction reachable with
    | initial => intro _; exact initial c h faulty time size faultBound
    | next prior party input allowed ih =>
      intro free
      obtain ⟨trail, tracked⟩ := ih (fun a b oa ob same =>
        free a b (occurs_mono party input oa) (occurs_mono party input ob) same)
      exact tracked_advance tracked size faultBound free allowed
  obtain ⟨trail, tracked⟩ := tracked
  exact ⟨localTrace trail, faithful_of_tracked tracked size⟩

theorem relative_agreement (initial : TrackedInitial) : RelativeAgreement :=
  relative_agreement_of_faithful (relative_faithful initial)

#assert_axioms faithful_of_tracked
#assert_axioms read_covered
#assert_axioms tracked_advance
#assert_axioms relative_faithful

end Minidregg.Verify.GenericSimplexRelativeFaithful
