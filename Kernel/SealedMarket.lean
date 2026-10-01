/-
# Kernel.SealedMarket — the sealed-bid market law (SEALED-MARKET; PRIVACY §3.4, MUD §2.7/§2.8)

One declared cell is one market: a founder sells `supply` units at one uniform price to at most
four sealed bids. This module is the law's **source**. The shell template
`deploy/shell/templates/market/sealed/law.market` is the Host's own rendering of `law`
(`LawLeaf.renderClause`, the text a refusal prints) with the parameters as placeholders, written by
`scripts/SealedMarketTemplate.lean`; the client binds the placeholders and parses it
(`native/resource-client/src/market.rs`), and `law show` prints an installed law back from the same
renderer. So the theorems below are about the law friends install, not a model beside it.

Fields (`fields.json`): 1 settled (0 → 1, once), 2 close, 3 revealEnd, 4 supply, 5 clearing price;
bid slot `k` at `16 + 8k`: who, commit, price, qty, blinder, filled.

Phases are request heights (`request/height`, the logical height; `valid_until` is a block height,
DECIDED 09-29): bids while `height ≤ close − 1`, reveals while `close ≤ height ≤ revealEnd − 1`,
settlement from `revealEnd`.

The theorems are the market's guarantees, each a consequence of one clause:
* `sealed_moves_no_opening` — while sealed, no admitted write moves any slot's price, quantity or
  blinder: nothing in the clear before the close. Pole: `early_reveal_refused`.
* `moved_opening_opens` / `market_reveal_binds` — an admitted write that moves a slot's opening
  opens that slot's commitment (`Pred.hashEq`, the whole tuple at once), so two admitted reveals of
  one commitment carry the same (price, qty, blinder) unless cSHAKE256 collides. Pole:
  `wrong_opening_refused`.
* `bid_only_sealed_empty_by_bidder` — a slot's bidder and commitment move only while sealed, only
  from an empty slot, only to the writer's own subject and a nonzero commitment. Pole:
  `late_bid_refused`.
* `fill_only_settling_within_qty` — a fill moves only in the settling write and never past the
  revealed quantity; an unrevealed slot (quantity 0) fills nothing. Pole: `overfill_refused`.
* `settles_once_by_founder_after_reveals` — the settling flag moves only 0 → 1, by the founder,
  after the last reveal height. Pole: `early_settle_refused`.
* `no_install_no_revoke` — the law admits no install and no revoke: neither the law nor a bidder's
  grant can be withdrawn mid-auction.

Hiding (that the commitment shows nothing of the bid) is `Pred.HashEqHiding`, ASSUMED and used by
no theorem here. What this module proves about privacy is only that the opening's fields do not
move before the close; that the Store holds no other copy of them is the journey's byte scan.
-/
import Pred.HashEq
import Theory.SheetLaw

namespace Minidregg.Kernel.SealedMarket

open Minidregg.Pred (Pred State eval Slot)
open Minidregg.Pred.HashEqDigest (Collision deployed)
open Minidregg.Theory.SheetLaw (ev_eq ev_le ev_eqSlots ev_leSlots ev_not ev_all ev_any)

set_option autoImplicit false

/-! ## §1. Slots, parameters, layout -/

def fA (n : Nat) : Slot := s!"resource/field/{n}/after"
def fB (n : Nat) : Slot := s!"resource/field/{n}/before"
def fD (n : Nat) : Slot := s!"resource/field/{n}/delta"
def heightSlot : Slot := "request/height"
def subjectSlot : Slot := "request/subject"
def verbSlot : Slot := "request/verb"

/-- The placeholders of the template. `lastSealed = close − 1` and `lastReveal = revealEnd − 1` on
every market the client opens (`market.rs` `law`); they are separate here so the template renders
each as its own placeholder. -/
structure Params where
  founder : Int
  lastSealed : Int
  lastReveal : Int
  close : Int
  revealEnd : Int
  supply : Int

/-- One bid slot's fields. -/
structure Bid where
  who : Nat
  commit : Nat
  price : Nat
  qty : Nat
  blinder : Nat
  filled : Nat

/-- Slot `k` is at `16 + 8k`. -/
def bid (k : Nat) : Bid :=
  ⟨16 + 8 * k, 16 + 8 * k + 1, 16 + 8 * k + 2, 16 + 8 * k + 3, 16 + 8 * k + 4, 16 + 8 * k + 5⟩

def slots : Nat := 4

def Bid.fields (b : Bid) : List Nat := [b.who, b.commit, b.price, b.qty, b.blinder, b.filled]

/-! ## §2. The law -/

/-- The write guard: a clause under it judges writes only (`LawLeaf.writeGuard`). -/
def guard : Pred := .not (.eq verbSlot 2)
/-- The market has been set up: field 2 was present before this write. -/
def setUp : Pred := .eqSlots (fB 2) (fB 2)
/-- The fields' deltas are all zero (each was present before and is unchanged). -/
def frozen (ns : List Nat) : Pred := Pred.all (ns.map fun n => .eq (fD n) 0)
def sealedNow (p : Params) : Pred := .le heightSlot p.lastSealed
def revealingNow (p : Params) : Pred := .le heightSlot p.lastReveal

/-- 0 management: reads and writes for any holder (the clauses below judge every write); the
founder delegates; nobody installs (4) or revokes (5). -/
def management (p : Params) : Pred :=
  Pred.any [.eq verbSlot 1, .eq verbSlot 2, Pred.all [.eq verbSlot 3, .eq subjectSlot p.founder]]

/-- 1 setup, once, by the founder: the parameters and every slot empty; then the parameters
are frozen. -/
def setup (p : Params) : Pred :=
  Pred.any [guard,
    Pred.all ([.not setUp, .eq subjectSlot p.founder, .eq (fA 1) 0, .eq (fA 2) p.close,
      .eq (fA 3) p.revealEnd, .eq (fA 4) p.supply, .eq (fA 5) 0] ++
      ((List.range slots).flatMap fun k => (bid k).fields.map fun n => .eq (fA n) 0)),
    Pred.all [setUp, .eq (fD 2) 0, .eq (fD 3) 0, .eq (fD 4) 0]]

/-- 2 settlement, once, by the founder, after the last reveal height. -/
def settlement (p : Params) : Pred :=
  Pred.any [guard, .not setUp, frozen [1, 5],
    Pred.all [.eq subjectSlot p.founder, .not (revealingNow p), .eq (fB 1) 0, .eq (fA 1) 1]]

/-- A bid: an empty slot takes its bidder and a nonzero commitment, only while sealed. -/
def bidRule (p : Params) (b : Bid) : Pred :=
  Pred.any [guard, .not setUp, frozen [b.who, b.commit],
    Pred.all [sealedNow p, .eq (fB b.who) 0, .eqSlots (fA b.who) subjectSlot,
      .eq (fB b.commit) 0, .not (.eq (fA b.commit) 0)]]

/-- The opened fields move only in the reveal window. -/
def windowRule (p : Params) (b : Bid) : Pred :=
  Pred.any [guard, .not setUp, frozen [b.price, b.qty, b.blinder],
    Pred.all [.not (sealedNow p), revealingNow p]]

/-- The atom a reveal of slot `b` must satisfy: the commitment opens to (price, qty) under the
blinder — one commitment, the whole tuple. -/
def opens (b : Bid) : Pred := .hashEq [fA b.price, fA b.qty] (fA b.blinder) (fA b.commit)

/-- A reveal opens the commitment. -/
def opensRule (b : Bid) : Pred :=
  Pred.any [guard, .not setUp, frozen [b.price, b.qty, b.blinder], opens b]

/-- The fill moves only in the settling write, and never past the revealed quantity. -/
def fillRule (b : Bid) : Pred :=
  Pred.any [guard, .not setUp, .eq (fD b.filled) 0,
    Pred.all [.eq (fB 1) 0, .eq (fA 1) 1, .not (.le (fA b.filled) (-1)), .leSlots (fA b.filled) (fA b.qty)]]

def slotRules (p : Params) (b : Bid) : List Pred :=
  [bidRule p b, windowRule p b, opensRule b, fillRule b]

def clauses (p : Params) : List Pred :=
  [management p, setup p, settlement p] ++ (List.range slots).flatMap fun k => slotRules p (bid k)

/-- The law of one market. -/
def law (p : Params) : Pred := Pred.all (clauses p)

/-- What each clause says, for the template's comment lines (one per clause, in order). -/
def notes : List String :=
  ["0 management: anyone holding a grant reads and writes (the clauses below judge every write); the founder delegates; nobody installs or revokes, so the law and the bidders' grants stand.",
   "1 setup, once, by the founder: the parameters and every bid slot empty; then the parameters are frozen.",
   "2 settlement, once, by the founder, after the last reveal height: settled 0 -> 1 and the clearing price."] ++
  (List.range slots).flatMap fun k =>
    let b := bid k
    let n := 3 + 4 * k
    [s!"{n} slot {k} (who {b.who}, commit {b.commit}, price {b.price}, qty {b.qty}, blinder {b.blinder}, filled {b.filled}): a bid takes an empty slot with the bidder and a nonzero commitment, only while sealed.",
     s!"{n + 1} slot {k}: the opened fields move only in the reveal window; nothing is in the clear while sealed.",
     s!"{n + 2} slot {k}: a reveal opens the commitment, the whole tuple at once, under its blinder.",
     s!"{n + 3} slot {k}: the fill moves only in the settling write, and never past the revealed quantity."]

theorem notes_length : notes.length = (clauses ⟨0, 0, 0, 0, 0, 0⟩).length := by decide

/-! ## §3. Reading the law -/

section Reading
variable {p : Params} {o n : State}

theorem law_clause (h : eval (law p) o n = true) {q : Pred} (hq : q ∈ clauses p) :
    eval q o n = true :=
  ev_all.mp h q hq

theorem slot_rule (h : eval (law p) o n = true) {k : Nat} (hk : k < slots) {q : Pred}
    (hq : q ∈ slotRules p (bid k)) : eval q o n = true :=
  law_clause h (List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, hq⟩))

/-- On a write to a set-up market, a guarded disjunction holds by one of its remaining branches. -/
theorem branch {rest : List Pred} (hw : n.get verbSlot = some 2) (hs : (n.get (fB 2)).isSome)
    (h : eval (Pred.any (guard :: .not setUp :: rest)) o n = true) :
    ∃ q ∈ rest, eval q o n = true := by
  obtain ⟨q, hq, hev⟩ := ev_any.mp h
  rcases List.mem_cons.mp hq with rfl | hq
  · exact absurd (ev_eq.mpr hw) (ev_not.mp hev)
  rcases List.mem_cons.mp hq with rfl | hq
  · exfalso; apply ev_not.mp hev; apply ev_eqSlots.mpr
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs; exact ⟨x, hx, hx⟩
  exact ⟨q, hq, hev⟩

theorem frozen_iff {ns : List Nat} :
    eval (frozen ns) o n = true ↔ ∀ m ∈ ns, n.get (fD m) = some 0 := by
  simp only [frozen, ev_all, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    ev_eq]

end Reading

/-! ## §4. The guarantees -/

section Guarantees
variable {p : Params} {o n : State}

/-- **Nothing in the clear while sealed.** An admitted write to a set-up market at a height up to
`lastSealed` moves no slot's price, quantity or blinder. -/
theorem sealed_moves_no_opening (h : eval (law p) o n = true) (hw : n.get verbSlot = some 2)
    (hs : (n.get (fB 2)).isSome) {t : Int} (ht : n.get heightSlot = some t) (hsealed : t ≤ p.lastSealed)
    {k : Nat} (hk : k < slots) :
    n.get (fD (bid k).price) = some 0 ∧ n.get (fD (bid k).qty) = some 0 ∧
      n.get (fD (bid k).blinder) = some 0 := by
  have hr := slot_rule h hk (q := windowRule p (bid k)) (by simp [slotRules])
  obtain ⟨q, hq, hev⟩ := branch hw hs hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · have := frozen_iff.mp hev; exact ⟨this _ (by simp), this _ (by simp), this _ (by simp)⟩
  · simp only [ev_all, List.forall_mem_cons, sealedNow] at hev
    exact absurd (ev_le.mpr ⟨t, ht, hsealed⟩) (ev_not.mp hev.1)

/-- Pole: a write at a sealed height that moves an opening field is refused. -/
theorem early_reveal_refused (hw : n.get verbSlot = some 2) (hs : (n.get (fB 2)).isSome)
    {t : Int} (ht : n.get heightSlot = some t) (hsealed : t ≤ p.lastSealed) {k : Nat}
    (hk : k < slots) (moved : n.get (fD (bid k).price) ≠ some 0) : eval (law p) o n = false := by
  cases he : eval (law p) o n
  · rfl
  · exact absurd (sealed_moves_no_opening he hw hs ht hsealed hk).1 moved

/-- **A moved opening opens the commitment.** An admitted write to a set-up market that moves any
of slot `k`'s price, quantity or blinder satisfies `opens` for that slot: the commitment field
holds the digest of the whole new tuple under the new blinder. -/
theorem moved_opening_opens (h : eval (law p) o n = true) (hw : n.get verbSlot = some 2)
    (hs : (n.get (fB 2)).isSome) {k : Nat} (hk : k < slots)
    (moved : ¬ (n.get (fD (bid k).price) = some 0 ∧ n.get (fD (bid k).qty) = some 0 ∧
      n.get (fD (bid k).blinder) = some 0)) :
    eval (opens (bid k)) o n = true := by
  have hr := slot_rule h hk (q := opensRule (bid k)) (by simp [slotRules])
  obtain ⟨q, hq, hev⟩ := branch hw hs hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · have := frozen_iff.mp hev
    exact absurd ⟨this _ (by simp), this _ (by simp), this _ (by simp)⟩ moved
  · exact hev

/-- **A reveal binds.** Two admitted writes to set-up markets that each move slot `k`'s opening and
show the same commitment value carry the same (price, qty) and the same blinder — unless cSHAKE256
collides. With `Pred.hashEq_context_bound` the same holds across cells: an opening admitted in one
market is no opening in another. -/
theorem market_reveal_binds {p' : Params} {o' n' : State} {k : Nat} (hk : k < slots)
    (h : eval (law p) o n = true) (hw : n.get verbSlot = some 2) (hs : (n.get (fB 2)).isSome)
    (moved : ¬ (n.get (fD (bid k).price) = some 0 ∧ n.get (fD (bid k).qty) = some 0 ∧
      n.get (fD (bid k).blinder) = some 0))
    (h' : eval (law p') o' n' = true) (hw' : n'.get verbSlot = some 2) (hs' : (n'.get (fB 2)).isSome)
    (moved' : ¬ (n'.get (fD (bid k).price) = some 0 ∧ n'.get (fD (bid k).qty) = some 0 ∧
      n'.get (fD (bid k).blinder) = some 0))
    (same : n.get (fA (bid k).commit) = n'.get (fA (bid k).commit)) :
    (n.get (fA (bid k).price) = n'.get (fA (bid k).price) ∧
      n.get (fA (bid k).qty) = n'.get (fA (bid k).qty) ∧
      n.get (fA (bid k).blinder) = n'.get (fA (bid k).blinder)) ∨ Collision deployed := by
  have e := moved_opening_opens h hw hs hk moved
  have e' := moved_opening_opens h' hw' hs' hk moved'
  rcases Minidregg.Pred.hashEq_reveal_binds_each e e' same with each | hcol
  · rcases Minidregg.Pred.hashEq_reveal_binds e e' same with ⟨-, hb⟩ | hcol
    · exact .inl ⟨each _ (by simp), each _ (by simp), hb⟩
    · exact .inr hcol
  · exact .inr hcol

/-- Pole: an admitted write cannot move slot `k`'s opening to fields that do not open its
commitment. -/
theorem wrong_opening_refused (hw : n.get verbSlot = some 2) (hs : (n.get (fB 2)).isSome)
    {k : Nat} (hk : k < slots)
    (moved : ¬ (n.get (fD (bid k).price) = some 0 ∧ n.get (fD (bid k).qty) = some 0 ∧
      n.get (fD (bid k).blinder) = some 0))
    (wrong : eval (opens (bid k)) o n = false) : eval (law p) o n = false := by
  cases he : eval (law p) o n
  · rfl
  · rw [moved_opening_opens he hw hs hk moved] at wrong; cases wrong

/-- **Bids only while sealed, only into an empty slot, only as oneself.** -/
theorem bid_only_sealed_empty_by_bidder (h : eval (law p) o n = true) (hw : n.get verbSlot = some 2)
    (hs : (n.get (fB 2)).isSome) {k : Nat} (hk : k < slots)
    (moved : ¬ (n.get (fD (bid k).who) = some 0 ∧ n.get (fD (bid k).commit) = some 0)) :
    (∃ t, n.get heightSlot = some t ∧ t ≤ p.lastSealed) ∧ n.get (fB (bid k).who) = some 0 ∧
      (∃ s, n.get (fA (bid k).who) = some s ∧ n.get subjectSlot = some s) ∧
      n.get (fB (bid k).commit) = some 0 ∧ n.get (fA (bid k).commit) ≠ some 0 := by
  have hr := slot_rule h hk (q := bidRule p (bid k)) (by simp [slotRules])
  obtain ⟨q, hq, hev⟩ := branch hw hs hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · have := frozen_iff.mp hev; exact absurd ⟨this _ (by simp), this _ (by simp)⟩ moved
  · simp only [ev_all, List.forall_mem_cons, sealedNow] at hev
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := hev
    exact ⟨ev_le.mp h1, ev_eq.mp h2, ev_eqSlots.mp h3, ev_eq.mp h4,
      fun hc => ev_not.mp h5 (ev_eq.mpr hc)⟩

/-- Pole: after the close, a write that moves a slot's bidder is refused. -/
theorem late_bid_refused (hw : n.get verbSlot = some 2) (hs : (n.get (fB 2)).isSome)
    {t : Int} (ht : n.get heightSlot = some t) (closed : p.lastSealed < t) {k : Nat}
    (hk : k < slots) (moved : n.get (fD (bid k).who) ≠ some 0) : eval (law p) o n = false := by
  cases he : eval (law p) o n
  · rfl
  · obtain ⟨⟨t', ht', hle⟩, -⟩ := bid_only_sealed_empty_by_bidder he hw hs hk (fun hh => moved hh.1)
    rw [ht] at ht'; cases ht'; omega

/-- **Fills only in the settling write, within the revealed quantity.** -/
theorem fill_only_settling_within_qty (h : eval (law p) o n = true) (hw : n.get verbSlot = some 2)
    (hs : (n.get (fB 2)).isSome) {k : Nat} (hk : k < slots)
    (moved : n.get (fD (bid k).filled) ≠ some 0) :
    n.get (fB 1) = some 0 ∧ n.get (fA 1) = some 1 ∧
      ∃ x y, n.get (fA (bid k).filled) = some x ∧ n.get (fA (bid k).qty) = some y ∧ 0 ≤ x ∧ x ≤ y := by
  have hr := slot_rule h hk (q := fillRule (bid k)) (by simp [slotRules])
  obtain ⟨q, hq, hev⟩ := branch hw hs hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact absurd (ev_eq.mp hev) moved
  · simp only [ev_all, List.forall_mem_cons] at hev
    obtain ⟨h1, h2, h3, h4, -⟩ := hev
    obtain ⟨x, y, hx, hy, hxy⟩ := ev_leSlots.mp h4
    refine ⟨ev_eq.mp h1, ev_eq.mp h2, x, y, hx, hy, ?_, hxy⟩
    by_contra hneg
    exact ev_not.mp h3 (ev_le.mpr ⟨x, hx, by omega⟩)

/-- Pole: a fill above the slot's quantity — any fill of an unrevealed slot, whose quantity is
0 — is refused. -/
theorem overfill_refused (hw : n.get verbSlot = some 2) (hs : (n.get (fB 2)).isSome) {k : Nat}
    (hk : k < slots) {x y : Int} (hx : n.get (fA (bid k).filled) = some x)
    (hy : n.get (fA (bid k).qty) = some y) (above : y < x) (moved : n.get (fD (bid k).filled) ≠ some 0) :
    eval (law p) o n = false := by
  cases he : eval (law p) o n
  · rfl
  · obtain ⟨-, -, x', y', hx', hy', -, hle⟩ := fill_only_settling_within_qty he hw hs hk moved
    rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'; omega

/-- **Settles once, by the founder, after the reveals.** -/
theorem settles_once_by_founder_after_reveals (h : eval (law p) o n = true)
    (hw : n.get verbSlot = some 2) (hs : (n.get (fB 2)).isSome)
    (moved : ¬ (n.get (fD 1) = some 0 ∧ n.get (fD 5) = some 0)) :
    n.get subjectSlot = some p.founder ∧ (∀ t, n.get heightSlot = some t → p.lastReveal < t) ∧
      n.get (fB 1) = some 0 ∧ n.get (fA 1) = some 1 := by
  have hr := law_clause h (q := settlement p) (by simp [clauses])
  obtain ⟨q, hq, hev⟩ := branch hw hs hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · have := frozen_iff.mp hev; exact absurd ⟨this _ (by simp), this _ (by simp)⟩ moved
  · simp only [ev_all, List.forall_mem_cons, revealingNow] at hev
    obtain ⟨h1, h2, h3, h4, -⟩ := hev
    refine ⟨ev_eq.mp h1, fun t ht => ?_, ev_eq.mp h3, ev_eq.mp h4⟩
    by_contra hle
    exact ev_not.mp h2 (ev_le.mpr ⟨t, ht, by omega⟩)

/-- Pole: a settling write at a reveal height is refused. -/
theorem early_settle_refused (hw : n.get verbSlot = some 2) (hs : (n.get (fB 2)).isSome)
    {t : Int} (ht : n.get heightSlot = some t) (open_ : t ≤ p.lastReveal)
    (moved : n.get (fD 1) ≠ some 0) : eval (law p) o n = false := by
  cases he : eval (law p) o n
  · rfl
  · have := (settles_once_by_founder_after_reveals he hw hs (fun hh => moved hh.1)).2.1 t ht
    omega

/-- **Nobody installs or revokes.** -/
theorem no_install_no_revoke (h : eval (law p) o n = true) :
    n.get verbSlot ≠ some 4 ∧ n.get verbSlot ≠ some 5 := by
  have hm := law_clause h (q := management p) (by simp [clauses])
  simp only [management, ev_any, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, ev_all] at hm
  rcases hm with h1 | h2 | h3
  · rw [ev_eq.mp h1]; decide
  · rw [ev_eq.mp h2]; decide
  · rw [ev_eq.mp (h3 _ (Or.inl rfl))]; decide

end Guarantees

/-! ## §5. Axiom pins — `Pred.eval` reaches the Keccak sponge (`[propext, Quot.sound]`). -/

/-- info: 'Minidregg.Kernel.SealedMarket.sealed_moves_no_opening' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sealed_moves_no_opening
/-- info: 'Minidregg.Kernel.SealedMarket.early_reveal_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms early_reveal_refused
/-- info: 'Minidregg.Kernel.SealedMarket.moved_opening_opens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms moved_opening_opens
/-- info: 'Minidregg.Kernel.SealedMarket.market_reveal_binds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms market_reveal_binds
/-- info: 'Minidregg.Kernel.SealedMarket.wrong_opening_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_opening_refused
/-- info: 'Minidregg.Kernel.SealedMarket.bid_only_sealed_empty_by_bidder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bid_only_sealed_empty_by_bidder
/-- info: 'Minidregg.Kernel.SealedMarket.late_bid_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms late_bid_refused
/-- info: 'Minidregg.Kernel.SealedMarket.fill_only_settling_within_qty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fill_only_settling_within_qty
/-- info: 'Minidregg.Kernel.SealedMarket.overfill_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms overfill_refused
/-- info: 'Minidregg.Kernel.SealedMarket.settles_once_by_founder_after_reveals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms settles_once_by_founder_after_reveals
/-- info: 'Minidregg.Kernel.SealedMarket.early_settle_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms early_settle_refused
/-- info: 'Minidregg.Kernel.SealedMarket.no_install_no_revoke' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_install_no_revoke

end Minidregg.Kernel.SealedMarket
