/-
# Compiler.Tower256ContentCert -- the content-bound automaton certificate, first instance

The statement of `zkml-research/docs/LEAF-PROVER-DECISION.md` §6 with the three amendments of
§6.1 (breadstuffs automata deputy), on the Tower256 leaf's own commitment:

* **Content.** `contentRoot` is the cSHAKE cube-Merkle root over the record's bytes, each byte a
  `Coordinate 8` leaf at its index, zero-padded to `2 ^ clog₂ length` leaves (`contentCommit`).
  It is the same `cubeRoot merkleDomainsC codecC` that commits a level-0 FRI word, so a succinct
  receipt for this statement opens the record's column under the statement's root.
* **Automaton (amendment 1).** The transition table is committed by a root that admits per-edge
  openings, not by a flat digest: `deltaRoot` is the cube-Merkle root of the dense table
  `key = 256 · state + byte ↦ next` (`deltaCommit`). A verifier that is given the table recomputes
  it (this file); a verifier of the attested shape opens one edge per byte (not here).
* **Claim (amendment 2).** `ClaimData` is `accept b | count n | bound lo hi`. This instance
  decides `accept`; the other two are refused (no relation is stated for them yet).
* **Encoding (amendment 3).** One canonical occupancy model: DENSE. Leaf `i` of a column is
  `Coord.ofNat 8 xᵢ` for `i` below the list's length, `Coordinate.zero 8` above it; depth is
  `Nat.clog 2 length`. A root alone does alias across lengths (`[]` and `[0]` share one, as do
  two all-zero tables of 3 and 4 states); what binds is the whole public tuple, with the record
  length and the state count as statement fields.

**The instance.** The receipt discloses the table and the word (`fullDisclosure`, the floor at
which breadstuffs' `Dfa.dfa_dial_wired` places the DFA kernel). `check_iff` is `decide` of the
relation, so it is exact and says nothing beyond it. The content is `named_or_collision`: for any
named table and record that commit to the statement, an accepted receipt IS them and decides the
claim about them, or the receipt's tree and the named tree collide at the two frames
`rootCollision` computes from them (the first node, top-down, with different framed inputs and
equal digests, or the differing leaf). The collision is pinned to the two trees, not an
existential over the suite, which pigeonhole would inhabit outright. It is never stated over
`BindingCommitment`/`PositionBinding` (§6).

Statement shape: PUBLIC METADATA. `deltaRoot` commits the transitions only; state count, initial
state and accepting set are statement fields in the clear. A private-policy root (amendment 1's
attested shape) has to authenticate those together with the transitions.

Differences from breadstuffs `Dfa`, not bridged by a theorem here: `DfaTable.run` is a fold, and
on the empty word the verdict is the initial state's, whereas `DfaAccepts` needs a nonempty trace;
an adapter to `BoundStatement` restricts to nonempty words and commits `(length, contentCommit)`.

Not here: a receipt that keeps the record private. That one is a Tower256 trace with an AIR and
the succinct FRI of `Tower256SuccinctCheck` over this `contentRoot`; no AIR layer exists yet.
-/

import Compiler.Tower256CshakeMerkleBinding
import Compiler.Tower256CoordinateMerkle
import Mathlib.Data.Nat.Log

namespace Minidregg.Compiler.Tower256ContentCert

open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Compiler.Tower256CshakeMerkleBinding
open Minidregg.Compiler.Tower256CoordinateMerkle
open Minidregg.Compiler.Tower256FinalPolynomialCheck (C8)
open Minidregg.Theory.BinaryTowerFanPaarCodec (Coordinate)
open Minidregg.Theory.BinaryCubeAddress (binaryAddressBits binaryCubeIndexEquiv)
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## Equal cube roots: equal columns, or a collision -/

/-- The two framed hash inputs, under one customization, that `rootCollision` names. -/
structure Frames where
  customization : List UInt8
  left : List UInt8
  right : List UInt8

/-- **The collision a pair of columns under one root exposes, computed from the two trees**: at
the first node (top-down) whose framed inputs differ but whose digests agree, or at the leaf
where the columns differ. It descends into the left half unless the left halves are equal. -/
def rootCollision {cshake : Cshake256} (domains : MerkleDomains cshake)
    {R : Type} [DecidableEq R] (codec : LawfulCodec R) :
    {k : Nat} → ((Fin k → Bool) → R) → ((Fin k → Bool) → R) → Frames
  | 0, col₁, col₂ =>
      ⟨domains.leafCustomization, leafInput codec (col₁ fun i => i.elim0),
        leafInput codec (col₂ fun i => i.elim0)⟩
  | _ + 1, col₁, col₂ =>
      let l₁ := fun t => col₁ (Fin.cases false t)
      let r₁ := fun t => col₁ (Fin.cases true t)
      let l₂ := fun t => col₂ (Fin.cases false t)
      let r₂ := fun t => col₂ (Fin.cases true t)
      if nodeInput cshake (cubeRoot domains codec l₁) (cubeRoot domains codec r₁) =
          nodeInput cshake (cubeRoot domains codec l₂) (cubeRoot domains codec r₂) then
        if l₁ = l₂ then rootCollision domains codec r₁ r₂ else rootCollision domains codec l₁ l₂
      else
        ⟨domains.nodeCustomization,
          nodeInput cshake (cubeRoot domains codec l₁) (cubeRoot domains codec r₁),
          nodeInput cshake (cubeRoot domains codec l₂) (cubeRoot domains codec r₂)⟩

/-- **Two columns under one cube root are the same column, or the frames `rootCollision` names
in those two trees collide.** -/
theorem cubeRoot_eq_or_collision {cshake : Cshake256} (domains : MerkleDomains cshake)
    {R : Type} [DecidableEq R] (codec : LawfulCodec R) :
    ∀ {k : Nat} (col₁ col₂ : (Fin k → Bool) → R),
      cubeRoot domains codec col₁ = cubeRoot domains codec col₂ →
        col₁ = col₂ ∨
          let w := rootCollision domains codec col₁ col₂
          FramedXofCollision cshake w.customization w.left w.right
  | 0, col₁, col₂, h => by
      by_cases hv : col₁ (fun i => i.elim0) = col₂ (fun i => i.elim0)
      · left
        funext a
        have ha : a = fun i => i.elim0 := funext fun i => i.elim0
        rw [ha]
        exact hv
      · exact Or.inr ⟨fun e => hv (leafInput_injective codec e), h⟩
  | k + 1, col₁, col₂, h => by
      simp only [rootCollision]
      split
      · rename_i e
        have hp := nodeInput_injective cshake
          (show (fun pair : Digest × Digest => nodeInput cshake pair.1 pair.2) (_, _) =
            (fun pair : Digest × Digest => nodeInput cshake pair.1 pair.2) (_, _) from e)
        have hl := congrArg Prod.fst hp
        have hr := congrArg Prod.snd hp
        simp only at hl hr
        split
        · rename_i hl'
          rcases cubeRoot_eq_or_collision domains codec _ _ hr with hr' | c
          · left
            funext a
            have ha : a = Fin.cons (a 0) (Fin.tail a) := (Fin.cons_self_tail a).symm
            rw [ha]
            generalize a 0 = b
            generalize Fin.tail a = t
            cases b
            · exact congrFun hl' t
            · exact congrFun hr' t
          · exact Or.inr c
        · rename_i hl'
          rcases cubeRoot_eq_or_collision domains codec _ _ hl with hl'' | c
          · exact absurd hl'' hl'
          · exact Or.inr c
      · rename_i e
        exact Or.inr ⟨e, h⟩

/-! ## Dense columns -/

def leafOfNat (n : Nat) : C8 := Coord.ofNat 8 n

/-- The canonical depth of a column of `n` entries. -/
def depthOf (n : Nat) : Nat := Nat.clog 2 n

/-- The dense column of a list: entry `i` at index `i`, zero leaves above the length. -/
def denseColumn (d : Nat) (l : List Nat) : (Fin d → Bool) → C8 :=
  fun address => leafOfNat (l.getD (binaryCubeIndexEquiv d address).val 0)

def denseRoot (l : List Nat) : Digest :=
  cubeRoot merkleDomainsC codecC (denseColumn (depthOf l.length) l)

theorem le_two_pow_depthOf (n : Nat) : n ≤ 2 ^ depthOf n := Nat.le_pow_clog (by norm_num) n

theorem leafOfNat_injective {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : leafOfNat a = leafOfNat b) : a = b := by
  have := congrArg (Coord.toNat 8) h
  unfold leafOfNat at this
  rwa [Coord.toNat_ofNat 8 a (by rw [capacity_eight]; exact ha),
    Coord.toNat_ofNat 8 b (by rw [capacity_eight]; exact hb)] at this

/-- Equal dense columns of two equally long lists of small entries: equal lists. -/
theorem denseColumn_injective (d : Nat) (l₁ l₂ : List Nat) (hlen : l₁.length = l₂.length)
    (hd : l₁.length ≤ 2 ^ d) (h₁ : ∀ x ∈ l₁, x < 2 ^ 256) (h₂ : ∀ x ∈ l₂, x < 2 ^ 256)
    (h : denseColumn d l₁ = denseColumn d l₂) : l₁ = l₂ := by
  apply List.ext_getElem hlen
  intro i hi₁ hi₂
  have hc := congrFun h (binaryAddressBits d ⟨i, by omega⟩)
  simp only [denseColumn, binaryAddressBits, Equiv.apply_symm_apply] at hc
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂,
    Option.getD_some] at hc
  exact leafOfNat_injective (h₁ _ (List.getElem_mem hi₁)) (h₂ _ (List.getElem_mem hi₂)) hc

/-- The frames two lists' dense trees name, at the first list's depth. -/
def denseCollision (l₁ l₂ : List Nat) : Frames :=
  rootCollision merkleDomainsC codecC (denseColumn (depthOf l₁.length) l₁)
    (denseColumn (depthOf l₁.length) l₂)

/-- The collision event at those frames. -/
def DenseCollision (l₁ l₂ : List Nat) : Prop :=
  let w := denseCollision l₁ l₂
  FramedXofCollision cshakeC w.customization w.left w.right

/-- Two equally long lists of small entries under one dense root are equal, or their two trees
collide at the frames `denseCollision` names. -/
theorem denseRoot_eq_or_collision (l₁ l₂ : List Nat) (hlen : l₁.length = l₂.length)
    (h₁ : ∀ x ∈ l₁, x < 2 ^ 256) (h₂ : ∀ x ∈ l₂, x < 2 ^ 256)
    (h : denseRoot l₁ = denseRoot l₂) :
    l₁ = l₂ ∨ DenseCollision l₁ l₂ := by
  unfold denseRoot at h
  rw [← hlen] at h
  rcases cubeRoot_eq_or_collision merkleDomainsC codecC _ _ h with hc | c
  · exact Or.inl (denseColumn_injective _ l₁ l₂ hlen (le_two_pow_depthOf _) h₁ h₂ hc)
  · exact Or.inr c

/-! ## The statement -/

/-- What a certificate claims about the record (§6.1 amendment 2). -/
inductive ClaimData where
  | accept (b : Bool)
  | count (n : Nat)
  | bound (lo hi : Nat)
  deriving DecidableEq, Repr

/-- **The content-bound statement** (data only). -/
structure ContentCert where
  contentRoot : Digest
  recordLength : Nat
  states : Nat
  initial : Nat
  accepting : List Bool
  deltaRoot : Digest
  claim : ClaimData
  deriving DecidableEq

/-- A byte automaton, dense: `delta[256 · s + b]` is the successor of state `s` on byte `b`. -/
structure DfaTable where
  states : Nat
  initial : Nat
  accepting : List Bool
  delta : List Nat
  deriving DecidableEq, Repr

namespace DfaTable

variable (t : DfaTable)

def WellFormed : Prop :=
  t.states ≤ 2 ^ 16 ∧ t.initial < t.states ∧ t.accepting.length = t.states ∧
    t.delta.length = t.states * 256 ∧ ∀ x ∈ t.delta, x < t.states

instance : Decidable t.WellFormed := by unfold WellFormed; infer_instance

def run (w : List UInt8) : Nat :=
  w.foldl (fun s b => t.delta.getD (256 * s + b.toNat) 0) t.initial

def accepts (w : List UInt8) : Bool := t.accepting.getD (t.run w) false

end DfaTable

def contentCommit (w : List UInt8) : Digest := denseRoot (w.map UInt8.toNat)

def deltaCommit (t : DfaTable) : Digest := denseRoot t.delta

/-- **The relation**: the table is well formed and is the statement's automaton, the word is the
statement's record, and the claim is the automaton's verdict on it. -/
def Holds (stmt : ContentCert) (t : DfaTable) (w : List UInt8) : Prop :=
  t.WellFormed ∧ t.states = stmt.states ∧ t.initial = stmt.initial ∧
    t.accepting = stmt.accepting ∧ deltaCommit t = stmt.deltaRoot ∧
    w.length = stmt.recordLength ∧ contentCommit w = stmt.contentRoot ∧
    stmt.claim = .accept (t.accepts w)

instance (stmt : ContentCert) (t : DfaTable) (w : List UInt8) : Decidable (Holds stmt t w) := by
  unfold Holds; infer_instance

/-- A named table and record that the statement commits to (no claim). -/
def Commits (stmt : ContentCert) (t : DfaTable) (w : List UInt8) : Prop :=
  t.WellFormed ∧ t.states = stmt.states ∧ t.initial = stmt.initial ∧
    t.accepting = stmt.accepting ∧ deltaCommit t = stmt.deltaRoot ∧
    w.length = stmt.recordLength ∧ contentCommit w = stmt.contentRoot

/-! ## The full-disclosure receipt -/

structure Receipt where
  table : DfaTable
  word : List UInt8
  deriving DecidableEq, Repr

def check (stmt : ContentCert) (r : Receipt) : Bool := decide (Holds stmt r.table r.word)

theorem check_iff (stmt : ContentCert) (r : Receipt) :
    check stmt r = true ↔ Holds stmt r.table r.word := decide_eq_true_iff

theorem byte_lt (w : List UInt8) : ∀ x ∈ w.map UInt8.toNat, x < 2 ^ 256 := by
  intro x hx
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
  exact lt_trans b.toNat_lt (by norm_num)

theorem delta_lt (t : DfaTable) (ht : t.WellFormed) : ∀ x ∈ t.delta, x < 2 ^ 256 := by
  intro x hx
  exact lt_of_lt_of_le (ht.2.2.2.2 x hx) (le_trans ht.1 (by norm_num))

/-- **An accepted receipt is the named table and record, and decides the claim about them; or
the receipt's tree and the named one collide at the frames `denseCollision` names** (the delta
trees, or the content trees). The form of breadstuffs' `Dfa.dfa_bound_identifies_record_or_collides`
with the equivocation pinned to the two trees. -/
theorem named_or_collision (stmt : ContentCert) (r : Receipt) (accepted : check stmt r = true)
    (t : DfaTable) (w : List UInt8) (named : Commits stmt t w) :
    (r.table = t ∧ r.word = w ∧ stmt.claim = .accept (t.accepts w)) ∨
      DenseCollision r.table.delta t.delta ∨
      DenseCollision (r.word.map UInt8.toNat) (w.map UInt8.toNat) := by
  obtain ⟨hwf, hs, hi, ha, hd, hl, hc, hclaim⟩ := (check_iff stmt r).mp accepted
  obtain ⟨twf, ts, ti, ta, td, tl, tc⟩ := named
  have hdelta : r.table.delta.length = t.delta.length := by
    rw [hwf.2.2.2.1, twf.2.2.2.1, hs, ts]
  rcases denseRoot_eq_or_collision _ _ hdelta (delta_lt _ hwf) (delta_lt _ twf)
      (show deltaCommit r.table = deltaCommit t by rw [hd, td]) with hδ | col
  · rcases denseRoot_eq_or_collision _ _ (by simp [hl, tl]) (byte_lt _) (byte_lt _)
        (show contentCommit r.word = contentCommit w by rw [hc, tc]) with hw | col
    · have ext : ∀ a b : DfaTable, a.states = b.states → a.initial = b.initial →
          a.accepting = b.accepting → a.delta = b.delta → a = b := by
        intro a b h1 h2 h3 h4
        cases a; cases b
        simp only at h1 h2 h3 h4
        subst h1 h2 h3 h4
        rfl
      have htab : r.table = t :=
        ext _ _ (hs.trans ts.symm) (hi.trans ti.symm) (ha.trans ta.symm) hδ
      have hword : r.word = w := List.map_injective_iff.mpr
        (fun a b h => UInt8.toNat_inj.mp h) hw
      left
      refine ⟨htab, hword, ?_⟩
      rw [hclaim, htab, hword]
    · exact Or.inr (Or.inr col)
  · exact Or.inr (Or.inl col)

/-! ## Teeth: absence of `ab` as the padded complement `neg(any* · ab · any*)` -/

/-- States: 0 nothing pending, 1 just read `a`, 2 read `ab` (dead). Accept unless dead. -/
def noAB : DfaTable where
  states := 3
  initial := 0
  accepting := [true, true, false]
  delta := (List.range (3 * 256)).map fun key =>
    let s := key / 256
    let b := key % 256
    if s = 2 then 2 else if b = 97 then 1 else if s = 1 ∧ b = 98 then 2 else 0

def bytesOf (s : String) : List UInt8 := s.toUTF8.toList

def stmtFor (t : DfaTable) (w : List UInt8) (claim : ClaimData) : ContentCert where
  contentRoot := contentCommit w
  recordLength := w.length
  states := t.states
  initial := t.initial
  accepting := t.accepting
  deltaRoot := deltaCommit t
  claim := claim

def clean : List UInt8 := bytesOf "xaxbba"
def dirty : List UInt8 := bytesOf "xxab"

#guard decide noAB.WellFormed
#guard noAB.accepts clean && !noAB.accepts dirty

-- Honest receipts are accepted, for both verdicts.
#guard check (stmtFor noAB clean (.accept true)) ⟨noAB, clean⟩
#guard check (stmtFor noAB dirty (.accept false)) ⟨noAB, dirty⟩

-- The wrong verdict is refused.
#guard !check (stmtFor noAB dirty (.accept true)) ⟨noAB, dirty⟩

-- A different record of the same length and the same verdict is refused by the content root
-- alone: every other conjunct of the relation holds for it.
#guard
  let other := bytesOf "xyab"
  let st := stmtFor noAB dirty (.accept false)
  noAB.accepts other == noAB.accepts dirty && other.length == st.recordLength &&
    contentCommit other != st.contentRoot && !check st ⟨noAB, other⟩

-- A forged table (edge `1 --b--> 0`) that would flip the verdict is refused by the delta root,
-- though it is well formed, agrees on every public field, and the claim matches its verdict.
-- The two delta trees are honest, so the frames `denseCollision` names differ in digest: the
-- collision disjunct of `named_or_collision` does not hold for them.
#guard
  let edited : DfaTable := { noAB with delta := noAB.delta.set (256 * 1 + 98) 0 }
  let f := denseCollision edited.delta noAB.delta
  decide edited.WellFormed && edited.accepts dirty &&
    !check (stmtFor noAB dirty (.accept true)) ⟨edited, dirty⟩ &&
    f.left != f.right &&
    cshakeC.xofDigest f.customization f.left != cshakeC.xofDigest f.customization f.right

-- Claims this instance does not decide are refused.
#guard !check (stmtFor noAB clean (.count 1)) ⟨noAB, clean⟩

-- The root alone aliases across lengths: `xab` and `xab ++ [0]` have one column and one root.
-- The statement binds the pair (length, root); the length field tells them apart.
#guard contentCommit (bytesOf "xab") == contentCommit (bytesOf "xab" ++ [0]) &&
  !check (stmtFor noAB (bytesOf "xab" ++ [0]) (.accept false)) ⟨noAB, bytesOf "xab"⟩ &&
  check (stmtFor noAB (bytesOf "xab" ++ [0]) (.accept false)) ⟨noAB, bytesOf "xab" ++ [0]⟩

/-- info: 'Minidregg.Compiler.Tower256ContentCert.named_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_or_collision

end Minidregg.Compiler.Tower256ContentCert
