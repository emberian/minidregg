/-
# Kernel.ChainHistory — the log chain at past heights, and the one certify rule over it

A certify record vouches for a prefix of the accepted log: "the first `h` records have
log-chain value `d`". Until now the rule accepted only `h` = the head and `d` = the head's
chain, so any write landing between a certifier's observation and its submission refused
the certify (`headMismatch`), and a steady writer could starve certification until the tail
bound refused every write. The rule here accepts any held prefix past the certified height:
the certifier names the newest head it observed, and a later write no longer refuses it.

**The interface.** The kernel reads past chain values only through `ChainHistory`, a class
the certify receiver (`Kernel.CertifyReceiver`) and the durable tail gate
(`Kernel.TailBound`) are generic over. An implementation answers `chainAt h` with the chain
after `h` accepted records, or `none` where it does not hold that height. Its one law
(`chainAt_le_head`): nothing is held past the head. What the values MEAN is the contract
`Faithful history truth`, stated against an abstract `truth : Nat → Digest` (the chain
after each prefix of the log), so this file imports no log representation: the durable
store proves `Faithful` for its own history against `DurableCheckpointCodec.chainAfter`.

**The rule** (`certifiable`): a certify of `(h, d)` over certified height `c` is admitted
exactly when `c < h` and the history holds `h` with value `d`. The receiver and the gate
both call it; there is no second copy.

Witnesses, built (by `decide` or by proof), not eyeballed:
* satisfiable: a prefix strictly below the head is admitted (`prefix_below_head_admitted`);
* teeth: at or below the certified height (`at_or_below_certified_refused`), past the head
  (`past_head_refused`), a held height with another chain value (`other_chain_refused`), and
  a height the history does not hold (`unheld_refused`) are each refused by name;
* premise inhabitation: `Faithful` is inhabited for every `truth` and head
  (`Prefixes.ofTruth_faithful`), so its consequences are not vacuous;
* the old rule is the special case: a faithful history admits the head at its true chain
  exactly when it advances (`head_admitted_iff`).

**What it buys, exactly.** A certify of a prefix ends starvation by concurrent writes: the
certifier's observed head stays certifiable however many records land after it. It does not
widen the tail bound: ordinary records are still admitted only while head − certified ≤ L
(`TailBound.tail_bounded`), so a certify of a prefix more than L below the head certifies a
true fact but reopens no writes. The certifier names the newest head it observed, which is
within L of the head whenever writes were being admitted at all.

**Implementations.** `Prefixes` (every prefix, below) is the reference; the durable store's
loaded image keeps its chain log (`DurableReceiverIO.Loaded`); `ChainHistory.Tip` holds only the head, for
a state that keeps no history (the light served path): it certifies the head and nothing
else, which is sound.
-/
module

public import Theory.TypedAuthorization
public import Theory.AxiomPin

@[expose] public section

namespace Minidregg.Kernel

open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- The log chain at past heights. `head` is the number of accepted records; `chainAt h`
is the chain value after the first `h` of them, where the implementation holds it. -/
class ChainHistory (H : Type) where
  head : H → Nat
  chainAt : H → Nat → Option Digest
  /-- Nothing is held past the head. -/
  chainAt_le_head : ∀ (history : H) (height : Nat) (digest : Digest),
    chainAt history height = some digest → height ≤ head history

namespace ChainHistory

variable {H : Type} [ChainHistory H]

/-- **The contract.** `history` is the history of a log whose chain after `h` records is
`truth h`: every value it holds is the true one, and it holds the head. -/
structure Faithful (history : H) (truth : Nat → Digest) : Prop where
  sound : ∀ height digest, chainAt history height = some digest → digest = truth height
  holdsHead : chainAt history (head history) = some (truth (head history))

/-! ## The rule -/

/-- Why a certify of a prefix is refused. -/
inductive Refusal where
  /-- The height is at or below the certified height. -/
  | notAdvancing
  /-- The history does not hold the height (past the head, or not kept). -/
  | heightUnavailable
  /-- The history holds the height with another chain value. -/
  | chainMismatch
  deriving DecidableEq, Repr

/-- **The certify rule.** Certify `(height, digest)` over certified height `certified`. -/
def certifiable (certified : Nat) (history : H) (height : Nat) (digest : Digest) :
    Except Refusal Unit :=
  if certified < height then
    match chainAt history height with
    | none => .error .heightUnavailable
    | some chain => if digest = chain then .ok () else .error .chainMismatch
  else .error .notAdvancing

theorem certifiable_ok_iff (certified : Nat) (history : H) (height : Nat) (digest : Digest) :
    certifiable certified history height digest = .ok () ↔
      certified < height ∧ chainAt history height = some digest := by
  unfold certifiable
  by_cases advancing : certified < height
  · simp only [advancing, if_true, true_and]
    cases held : chainAt history height with
    | none => simp
    | some chain =>
        by_cases same : digest = chain
        · subst same; simp
        · simp [same, Ne.symm same]
  · simp [advancing]

/-- **Soundness against the log.** An admitted certify names a height past the certified
one, at or below the head, with the log's true chain value there. -/
theorem certifiable_sound {certified : Nat} {history : H} {height : Nat} {digest : Digest}
    {truth : Nat → Digest} (faithful : Faithful history truth)
    (ok : certifiable certified history height digest = .ok ()) :
    certified < height ∧ height ≤ head history ∧ digest = truth height := by
  obtain ⟨advancing, held⟩ := (certifiable_ok_iff certified history height digest).mp ok
  exact ⟨advancing, chainAt_le_head history height digest held, faithful.sound height digest held⟩

/-! ## Teeth -/

theorem at_or_below_certified_refused (certified : Nat) (history : H) (height : Nat)
    (digest : Digest) (behind : height ≤ certified) :
    certifiable certified history height digest = .error .notAdvancing := by
  unfold certifiable
  simp [Nat.not_lt.mpr behind]

theorem unheld_refused (certified : Nat) (history : H) (height : Nat) (digest : Digest)
    (advancing : certified < height) (unheld : chainAt history height = none) :
    certifiable certified history height digest = .error .heightUnavailable := by
  unfold certifiable
  simp [advancing, unheld]

theorem past_head_refused (certified : Nat) (history : H) (height : Nat) (digest : Digest)
    (advancing : certified < height) (past : head history < height) :
    certifiable certified history height digest = .error .heightUnavailable := by
  apply unheld_refused certified history height digest advancing
  cases held : chainAt history height with
  | none => rfl
  | some chain => exact absurd (chainAt_le_head history height chain held) (Nat.not_le.mpr past)

theorem other_chain_refused (certified : Nat) (history : H) (height : Nat) (digest chain : Digest)
    (advancing : certified < height) (held : chainAt history height = some chain)
    (other : digest ≠ chain) :
    certifiable certified history height digest = .error .chainMismatch := by
  unfold certifiable
  simp [advancing, held, other]

/-- Against a faithful history: a certify naming anything but the log's true chain value
at that height is refused. -/
theorem untrue_refused {certified : Nat} {history : H} {height : Nat} {digest : Digest}
    {truth : Nat → Digest} (faithful : Faithful history truth) (untrue : digest ≠ truth height) :
    certifiable certified history height digest ≠ .ok () :=
  fun ok => untrue (certifiable_sound faithful ok).2.2

/-- The old rule is the special case: a faithful history admits the head at its true
chain exactly when it advances. -/
theorem head_admitted_iff {certified : Nat} {history : H} {truth : Nat → Digest}
    (faithful : Faithful history truth) :
    certifiable certified history (head history) (truth (head history)) = .ok () ↔
      certified < head history := by
  rw [certifiable_ok_iff]
  exact ⟨fun both => both.1, fun advancing => ⟨advancing, faithful.holdsHead⟩⟩

end ChainHistory

/-! ## The reference implementation: every prefix's chain, in order -/

/-- `values[h]` is the chain after `h` records; the head is `values.length - 1`. -/
structure Prefixes where
  values : List Digest

instance : ChainHistory Prefixes where
  head prefixes := prefixes.values.length - 1
  chainAt prefixes height := if height + 1 ≤ prefixes.values.length then prefixes.values[height]? else none
  chainAt_le_head prefixes height digest held := by
    by_cases within : height + 1 ≤ prefixes.values.length
    · omega
    · simp [within] at held

namespace Prefixes

/-- The history of a log of `head` records whose chain after `h` records is `truth h`. -/
def ofTruth (truth : Nat → Digest) (head : Nat) : Prefixes :=
  ⟨(List.range (head + 1)).map truth⟩

theorem ofTruth_head (truth : Nat → Digest) (head : Nat) :
    ChainHistory.head (ofTruth truth head) = head := by
  simp [ChainHistory.head, ofTruth]

/-- **Premise inhabitation.** `Faithful` holds of a real history for every log. -/
theorem ofTruth_faithful (truth : Nat → Digest) (head : Nat) :
    ChainHistory.Faithful (ofTruth truth head) truth := by
  refine ⟨?_, ?_⟩
  · intro height digest held
    simp only [ChainHistory.chainAt, ofTruth, List.length_map, List.length_range] at held
    by_cases within : height + 1 ≤ head + 1
    · have lt : height < head + 1 := by omega
      rw [if_pos within, List.getElem?_map, List.getElem?_range lt] at held
      exact (Option.some.inj held).symm
    · simp [within] at held
  · simp only [ChainHistory.chainAt, ChainHistory.head, ofTruth, List.length_map, List.length_range]
    simp

end Prefixes

/-! ## A history that holds only the head -/

/-- The head and its chain: all a state without history knows. -/
structure ChainHistory.Tip where
  height : Nat
  chain : Digest

instance : ChainHistory ChainHistory.Tip where
  head tip := tip.height
  chainAt tip height := if height = tip.height then some tip.chain else none
  chainAt_le_head tip height digest held := by
    by_cases at_ : height = tip.height
    · omega
    · simp [at_] at held

/-- A tip whose chain is the log's chain at its height is faithful to that log. -/
theorem ChainHistory.Tip.faithful (truth : Nat → Digest) (tip : ChainHistory.Tip) (exact : tip.chain = truth tip.height) :
    ChainHistory.Faithful tip truth := by
  refine ⟨?_, ?_⟩
  · intro height digest held
    simp only [ChainHistory.chainAt] at held
    by_cases at_ : height = tip.height
    · rw [if_pos at_] at held
      rw [at_, ← exact]; exact (Option.some.inj held).symm
    · simp [at_] at held
  · simp [ChainHistory.chainAt, ChainHistory.head, exact]

/-! ## Built witnesses -/

namespace ChainHistory

/-- A log of five records; chain after `h` records is `⟨10 + h⟩`. -/
private def five : Prefixes := ⟨[⟨10⟩, ⟨11⟩, ⟨12⟩, ⟨13⟩, ⟨14⟩, ⟨15⟩]⟩

/-- **Satisfiable** (and the new liveness): certified at 2, head 5, a certify of the
prefix 3 at its chain is admitted. -/
theorem prefix_below_head_admitted : certifiable 2 five 3 ⟨13⟩ = .ok () := rfl

/-- The head itself is still admitted. -/
theorem head_admitted : certifiable 2 five 5 ⟨15⟩ = .ok () := rfl

/-- Teeth, concrete: past the head, a wrong chain, at the certified height. -/
theorem past_head_refused_6 : certifiable 2 five 6 ⟨16⟩ = .error .heightUnavailable := rfl
theorem wrong_chain_refused_3 : certifiable 2 five 3 ⟨15⟩ = .error .chainMismatch := rfl
theorem at_certified_refused_2 : certifiable 2 five 2 ⟨12⟩ = .error .notAdvancing := rfl

/-- The witness history is the faithful history of its log. -/
theorem five_faithful : Faithful five (fun h => ⟨10 + h⟩) := by
  have : five = Prefixes.ofTruth (fun h => ⟨10 + h⟩) 5 := rfl
  rw [this]
  exact Prefixes.ofTruth_faithful _ _

#assert_axioms certifiable_ok_iff certifiable_sound at_or_below_certified_refused unheld_refused
  past_head_refused other_chain_refused untrue_refused head_admitted_iff
  Prefixes.ofTruth_faithful prefix_below_head_admitted head_admitted past_head_refused_6
  wrong_chain_refused_3 at_certified_refused_2 five_faithful Tip.faithful

end ChainHistory

end Minidregg.Kernel
