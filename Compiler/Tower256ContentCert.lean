/-
# Compiler.Tower256ContentCert -- the content-bound automaton certificate, first instance

The statement of `zkml-research/docs/LEAF-PROVER-DECISION.md` §6 with the three amendments of
§6.1 (breadstuffs automata deputy), on the Tower256 leaf's own commitment:

* **Content.** `contentRoot` is the cSHAKE cube-Merkle root over the record's bytes, each byte a
  `Coordinate 8` leaf at its index, zero-padded to `2 ^ clog₂ length` leaves (`contentCommit`).
  It is the same `cubeRoot merkleDomainsC codecC` that commits a level-0 FRI word, so a succinct
  receipt for this statement opens the record's column under the statement's root.
* **Automaton (amendment 1).** `automatonRoot` commits the whole automaton: the cSHAKE, under its
  own customization, of the framed state count, initial state, accepting set and `deltaCommit`,
  the cube-Merkle root of the dense table `key = 256 · state + byte ↦ next`. The transitions stay
  openable one edge at a time under `deltaCommit`; nothing about the automaton is in the clear.
  A verifier that is given the table recomputes both (this file); a verifier of the attested
  shape opens one edge per byte (not here).
* **Claim (amendment 2).** `ClaimData` is `accept b | count n | bound lo hi`. This instance
  decides `accept`; the other two are refused (no relation is stated for them yet).
* **Encoding (amendment 3).** One canonical occupancy model: DENSE. Leaf `i` of a column is
  `Coord.ofNat 8 xᵢ` for `i` below the list's length, `Coordinate.zero 8` above it; depth is
  `Nat.clog 2 length`. A root alone does alias across lengths (`[]` and `[0]` share one, as do
  two all-zero tables of 3 and 4 states). The record length is a statement field and the state
  count is inside the automaton frame, so neither alias reaches the statement.

**The instance.** The receipt discloses the table and the word (`fullDisclosure`, the floor at
which breadstuffs' `Dfa.dfa_dial_wired` places the DFA kernel). `check_iff` is `decide` of the
relation, so it is exact and says nothing beyond it. The content is `named_or_collision`: for any
named table and record that commit to the statement, an accepted receipt IS them and decides the
claim about them, or the two automaton frames collide, or the receipt's tree and the named tree
collide at the two frames `rootCollision` computes from them (the first node, top-down, with different framed inputs and
equal digests, or the differing leaf). The collision is pinned to the two trees, not an
existential over the suite, which pigeonhole would inhabit outright. It is never stated over
`BindingCommitment`/`PositionBinding` (§6).

Breadstuffs' run semantics: a run there is a NONEMPTY list of steps (`Dfa.DfaAccepts`), so the
relation requires a nonempty record, and `accepts_iff_dfaAccepts` proves that on a nonempty word
the table's fold accepts exactly when `DfaAccepts` (restated as `Bread.DfaAccepts`, since this
package cannot import breadstuffs) has a run reading the word under the table's own transition
relation, initial state and accepting set. `named_dfaAccepts_or_collision` is the
`dfa_bound_identifies_record_or_collides` shape. An adapter to `BoundStatement` commits
`(length, contentCommit)`.

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
  automatonRoot : Digest
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

/-! ## Breadstuffs' run semantics, and the table's run inside it

Restated from breadstuffs `metatheory/Dregg2/Crypto/Dfa.lean` at `19d6da41f` (`Step`,
`stepValid`, `chained` as `Hypergraph.chain`, `DfaAccepts`, `traceWord`): that package is on
another toolchain and cannot be imported here. A run there is a NONEMPTY list of steps. The
relation `Holds` therefore requires a nonempty record, and `accepts_iff_dfaAccepts` says the
table's fold accepts a nonempty word exactly when breadstuffs' `DfaAccepts` has a run reading it,
for the table's own transition relation, initial state and accepting set. -/

namespace Bread

structure Step (State Sym : Type) where
  state : State
  sym : Sym
  next : State

def chain {α : Type} (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => R a b ∧ chain R (b :: rest)

def DfaAccepts {State Sym : Type} (δ : State → Sym → State → Prop) (q₀ : State)
    (accept : State → Prop) (trace : List (Step State Sym)) : Prop :=
  ∃ first last,
    trace.head? = some first ∧
    trace.getLast? = some last ∧
    first.state = q₀ ∧
    accept last.next ∧
    (∀ s ∈ trace, δ s.state s.sym s.next) ∧
    chain (fun a b => b.state = a.next) trace

def traceWord {State Sym : Type} (trace : List (Step State Sym)) : List Sym := trace.map (·.sym)

end Bread

namespace DfaTable

variable (t : DfaTable)

def step (s : Nat) (b : UInt8) : Nat := t.delta.getD (256 * s + b.toNat) 0

/-- The table's transition relation, as breadstuffs' `δ`. -/
def δ : Nat → UInt8 → Nat → Prop := fun s b n => n = t.step s b

/-- The table's accept predicate, as breadstuffs' `accept`. -/
def acceptP : Nat → Prop := fun s => t.accepting.getD s false = true

/-- The run of the table from `s` over `w`, as breadstuffs steps. -/
def traceFrom : Nat → List UInt8 → List (Bread.Step Nat UInt8)
  | _, [] => []
  | s, b :: rest => ⟨s, b, t.step s b⟩ :: traceFrom (t.step s b) rest

theorem traceWord_traceFrom : ∀ (s : Nat) (w : List UInt8), Bread.traceWord (t.traceFrom s w) = w
  | _, [] => rfl
  | s, b :: rest => congrArg (List.cons b) (traceWord_traceFrom (t.step s b) rest)

theorem valid_traceFrom : ∀ (s : Nat) (w : List UInt8),
    ∀ x ∈ t.traceFrom s w, t.δ x.state x.sym x.next
  | _, [] => by simp [traceFrom]
  | s, b :: rest => by
      intro x hx
      simp only [traceFrom, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rfl
      · exact valid_traceFrom (t.step s b) rest x hx

theorem chain_traceFrom : ∀ (s : Nat) (w : List UInt8),
    Bread.chain (fun a b => b.state = a.next) (t.traceFrom s w)
  | _, [] => trivial
  | _, [_] => trivial
  | s, b :: c :: rest => ⟨rfl, chain_traceFrom (t.step s b) (c :: rest)⟩

theorem last_traceFrom : ∀ (s : Nat) (b : UInt8) (rest : List UInt8),
    ∃ last, (t.traceFrom s (b :: rest)).getLast? = some last ∧
      last.next = (b :: rest).foldl t.step s
  | _, _, [] => ⟨_, rfl, rfl⟩
  | s, b, c :: rest => by
      obtain ⟨l, hl, hn⟩ := last_traceFrom (t.step s b) c rest
      refine ⟨l, ?_, hn⟩
      simp only [traceFrom] at hl ⊢
      rw [List.getLast?_cons_cons]
      exact hl

/-- A valid chained run from `s` is the table's run from `s` over its own word. -/
theorem eq_traceFrom : ∀ (s : Nat) (tr : List (Bread.Step Nat UInt8)),
    (∀ x ∈ tr, t.δ x.state x.sym x.next) →
    Bread.chain (fun a b => b.state = a.next) tr →
    (∀ x, tr.head? = some x → x.state = s) →
    tr = t.traceFrom s (Bread.traceWord tr)
  | _, [], _, _, _ => rfl
  | s, [x], hv, _, hh => by
      have h1 := hh x rfl
      have h2 := hv x (by simp)
      obtain ⟨xs, xb, xn⟩ := x
      simp only at h1 h2
      subst h1 h2
      rfl
  | s, x :: y :: rest, hv, hc, hh => by
      have h1 := hh x rfl
      have h2 := hv x (by simp)
      have ih := eq_traceFrom x.next (y :: rest)
        (fun z hz => hv z (List.mem_cons_of_mem _ hz)) hc.2
        (fun z hz => by
          simp only [List.head?_cons, Option.some.injEq] at hz
          subst hz
          exact hc.1)
      obtain ⟨xs, xb, xn⟩ := x
      simp only at h1 h2 ih
      subst h1 h2
      exact congrArg (List.cons _) ih

/-- **On a nonempty word, the table's verdict is breadstuffs' acceptance.** -/
theorem accepts_iff_dfaAccepts (w : List UInt8) (hw : w ≠ []) :
    t.accepts w = true ↔
      ∃ trace, Bread.DfaAccepts t.δ t.initial t.acceptP trace ∧ Bread.traceWord trace = w := by
  obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil hw
  constructor
  · intro hacc
    obtain ⟨l, hl, hn⟩ := t.last_traceFrom t.initial b rest
    refine ⟨t.traceFrom t.initial (b :: rest),
      ⟨_, l, rfl, hl, rfl, ?_, t.valid_traceFrom _ _, t.chain_traceFrom _ _⟩,
      t.traceWord_traceFrom _ _⟩
    show t.accepting.getD l.next false = true
    rw [hn]
    exact hacc
  · rintro ⟨tr, ⟨first, last, hf, hl, hq, ha, hv, hc⟩, hwd⟩
    have htr := t.eq_traceFrom t.initial tr hv hc (fun x hx => by
      rw [hf, Option.some.injEq] at hx
      subst hx
      exact hq)
    rw [hwd] at htr
    subst htr
    obtain ⟨l, hl', hn⟩ := t.last_traceFrom t.initial b rest
    have hll : l = last := Option.some.inj (hl'.symm.trans hl)
    show t.accepting.getD (t.run (b :: rest)) false = true
    have : t.run (b :: rest) = last.next := by rw [← hll]; exact hn.symm
    rw [this]
    exact ha

end DfaTable

def contentCommit (w : List UInt8) : Digest := denseRoot (w.map UInt8.toNat)

def deltaCommit (t : DfaTable) : Digest := denseRoot t.delta

theorem byte_lt (w : List UInt8) : ∀ x ∈ w.map UInt8.toNat, x < 2 ^ 256 := by
  intro x hx
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
  exact lt_trans b.toNat_lt (by norm_num)

theorem delta_lt (t : DfaTable) (ht : t.WellFormed) : ∀ x ∈ t.delta, x < 2 ^ 256 := by
  intro x hx
  exact lt_of_lt_of_le (ht.2.2.2.2 x hx) (le_trans ht.1 (by norm_num))

/-! ## The automaton root

The whole automaton is committed by one digest: the state count, the initial state, the
accepting set and the transitions' dense root, framed and hashed under their own customization.
The transitions stay openable one edge at a time under `deltaCommit`, which travels inside the
frame. -/

def automatonCustomization : List UInt8 :=
  0x05 :: Tower256ConcreteBackend.utf8 "MINIDREGG/TOWER256/CONTENTCERT/AUTOMATON/V1"

def acceptBytes (accepting : List Bool) : List UInt8 :=
  accepting.map fun b => if b then 1 else 0

/-- The framed preimage of the automaton root. -/
def automatonInput (t : DfaTable) : List UInt8 :=
  envelope (envelope (codecC.encode (leafOfNat t.states)) ++
      envelope (codecC.encode (leafOfNat t.initial))) ++
    envelope (envelope (acceptBytes t.accepting) ++
      envelope (cshakeC.digestCodec.encode (deltaCommit t)))

def automatonCommit (t : DfaTable) : Digest :=
  cshakeC.xofDigest automatonCustomization (automatonInput t)

theorem acceptBytes_injective : Function.Injective acceptBytes := by
  intro a b h
  apply List.map_injective_iff.mpr _ h
  intro x y hxy
  cases x <;> cases y <;> simp_all

theorem pair_eq {a b c d : List UInt8} (h : envelope a ++ envelope b = envelope c ++ envelope d) :
    a = c ∧ b = d := by
  have := envelopePair_injective
    (show (fun pair : List UInt8 × List UInt8 => envelope pair.1 ++ envelope pair.2) (a, b) =
      (fun pair : List UInt8 × List UInt8 => envelope pair.1 ++ envelope pair.2) (c, d) from h)
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- Equal framed automaton inputs of well-formed tables: equal metadata and equal delta roots. -/
theorem automatonInput_injective (t₁ t₂ : DfaTable) (h₁ : t₁.WellFormed) (h₂ : t₂.WellFormed)
    (h : automatonInput t₁ = automatonInput t₂) :
    t₁.states = t₂.states ∧ t₁.initial = t₂.initial ∧ t₁.accepting = t₂.accepting ∧
      deltaCommit t₁ = deltaCommit t₂ := by
  have hs₁ : t₁.states < 2 ^ 256 := lt_of_le_of_lt h₁.1 (by norm_num)
  have hs₂ : t₂.states < 2 ^ 256 := lt_of_le_of_lt h₂.1 (by norm_num)
  obtain ⟨hm, ha⟩ := pair_eq h
  obtain ⟨hs, hi⟩ := pair_eq hm
  obtain ⟨hacc, hd⟩ := pair_eq ha
  refine ⟨leafOfNat_injective hs₁ hs₂ (lawfulCodec_encode_injective codecC hs),
    leafOfNat_injective (lt_trans h₁.2.1 hs₁) (lt_trans h₂.2.1 hs₂)
      (lawfulCodec_encode_injective codecC hi),
    acceptBytes_injective hacc, lawfulCodec_encode_injective _ hd⟩

/-- The collision event at two automaton frames. -/
def AutomatonCollision (t₁ t₂ : DfaTable) : Prop :=
  FramedXofCollision cshakeC automatonCustomization (automatonInput t₁) (automatonInput t₂)

/-- **One automaton root, one automaton**: two well-formed tables under one root are the same
table, or their automaton frames collide, or their delta trees collide at the frames
`denseCollision` names. -/
theorem automatonCommit_eq_or_collision (t₁ t₂ : DfaTable) (h₁ : t₁.WellFormed)
    (h₂ : t₂.WellFormed) (h : automatonCommit t₁ = automatonCommit t₂) :
    t₁ = t₂ ∨ AutomatonCollision t₁ t₂ ∨ DenseCollision t₁.delta t₂.delta := by
  by_cases e : automatonInput t₁ = automatonInput t₂
  · obtain ⟨hs, hi, ha, hd⟩ := automatonInput_injective t₁ t₂ h₁ h₂ e
    have hlen : t₁.delta.length = t₂.delta.length := by rw [h₁.2.2.2.1, h₂.2.2.2.1, hs]
    rcases denseRoot_eq_or_collision _ _ hlen (delta_lt _ h₁) (delta_lt _ h₂) hd with hδ | c
    · left
      cases t₁; cases t₂
      simp only at hs hi ha hδ
      subst hs hi ha hδ
      rfl
    · exact Or.inr (Or.inr c)
  · exact Or.inr (Or.inl ⟨e, h⟩)

/-- **The relation**: the table is well formed and is the statement's automaton, the word is the
statement's record, and the claim is the automaton's verdict on it. -/
def Holds (stmt : ContentCert) (t : DfaTable) (w : List UInt8) : Prop :=
  t.WellFormed ∧ automatonCommit t = stmt.automatonRoot ∧ w ≠ [] ∧
    w.length = stmt.recordLength ∧ contentCommit w = stmt.contentRoot ∧
    stmt.claim = .accept (t.accepts w)

instance (stmt : ContentCert) (t : DfaTable) (w : List UInt8) : Decidable (Holds stmt t w) := by
  unfold Holds; infer_instance

/-- A named table and record that the statement commits to (no claim). -/
def Commits (stmt : ContentCert) (t : DfaTable) (w : List UInt8) : Prop :=
  t.WellFormed ∧ automatonCommit t = stmt.automatonRoot ∧
    w.length = stmt.recordLength ∧ contentCommit w = stmt.contentRoot

/-! ## The full-disclosure receipt -/

structure Receipt where
  table : DfaTable
  word : List UInt8
  deriving DecidableEq, Repr

def check (stmt : ContentCert) (r : Receipt) : Bool := decide (Holds stmt r.table r.word)

theorem check_iff (stmt : ContentCert) (r : Receipt) :
    check stmt r = true ↔ Holds stmt r.table r.word := decide_eq_true_iff

/-- **An accepted receipt is the named table and record, and decides the claim about them; or
the receipt's tree and the named one collide at the frames `denseCollision` names** (the delta
trees, or the content trees). The form of breadstuffs' `Dfa.dfa_bound_identifies_record_or_collides`
with the equivocation pinned to the two trees. -/
theorem named_or_collision (stmt : ContentCert) (r : Receipt) (accepted : check stmt r = true)
    (t : DfaTable) (w : List UInt8) (named : Commits stmt t w) :
    (r.table = t ∧ r.word = w ∧ stmt.claim = .accept (t.accepts w)) ∨
      AutomatonCollision r.table t ∨
      DenseCollision r.table.delta t.delta ∨
      DenseCollision (r.word.map UInt8.toNat) (w.map UInt8.toNat) := by
  obtain ⟨hwf, ha, -, hl, hc, hclaim⟩ := (check_iff stmt r).mp accepted
  obtain ⟨twf, ta, tl, tc⟩ := named
  rcases automatonCommit_eq_or_collision _ _ hwf twf (by rw [ha, ta]) with htab | c | c
  · rcases denseRoot_eq_or_collision _ _ (by simp [hl, tl]) (byte_lt _) (byte_lt _)
        (show contentCommit r.word = contentCommit w by rw [hc, tc]) with hw | col
    · have hword : r.word = w := List.map_injective_iff.mpr
        (fun a b h => UInt8.toNat_inj.mp h) hw
      left
      refine ⟨htab, hword, ?_⟩
      rw [hclaim, htab, hword]
    · exact Or.inr (Or.inr (Or.inr col))
  · exact Or.inr (Or.inl c)
  · exact Or.inr (Or.inr (Or.inl c))

/-- **The breadstuffs form.** An accepted receipt claiming acceptance gives, for any named table
and record the statement commits to, a run of `Dfa.DfaAccepts` (restated as `Bread.DfaAccepts`)
for the named table that reads the named record; or one of the three named collisions. -/
theorem named_dfaAccepts_or_collision (stmt : ContentCert) (r : Receipt)
    (accepted : check stmt r = true) (hclaim : stmt.claim = .accept true)
    (t : DfaTable) (w : List UInt8) (named : Commits stmt t w) :
    (∃ trace, Bread.DfaAccepts t.δ t.initial t.acceptP trace ∧ Bread.traceWord trace = w) ∨
      AutomatonCollision r.table t ∨
      DenseCollision r.table.delta t.delta ∨
      DenseCollision (r.word.map UInt8.toNat) (w.map UInt8.toNat) := by
  have hne : w ≠ [] := by
    obtain ⟨-, -, hrw, hrl, -⟩ := (check_iff stmt r).mp accepted
    intro hw
    apply hrw
    apply List.eq_nil_of_length_eq_zero
    rw [hrl, ← named.2.2.1, hw]
    rfl
  rcases named_or_collision stmt r accepted t w named with ⟨-, -, hc⟩ | c
  · left
    rw [hclaim] at hc
    exact (t.accepts_iff_dfaAccepts w hne).mp (ClaimData.accept.inj hc).symm
  · exact Or.inr c

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
  automatonRoot := automatonCommit t
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

-- The automaton root covers the accepting set and the initial state: tables with the same
-- transitions (same delta root) but another accepting set, or another initial state, are
-- refused by the automaton root alone, with the claim matching their own verdict.
#guard
  let acc : DfaTable := { noAB with accepting := [true, true, true] }
  let ini : DfaTable := { noAB with initial := 2 }
  deltaCommit acc == deltaCommit noAB && decide acc.WellFormed && acc.accepts dirty &&
    !check (stmtFor noAB dirty (.accept true)) ⟨acc, dirty⟩ &&
    deltaCommit ini == deltaCommit noAB && decide ini.WellFormed && !ini.accepts clean &&
    !check (stmtFor noAB clean (.accept false)) ⟨ini, clean⟩

-- The empty record is refused even with the initial state's verdict as claim: breadstuffs'
-- runs are nonempty.
#guard noAB.accepts [] && !check (stmtFor noAB [] (.accept true)) ⟨noAB, []⟩

-- The table's run on `clean`, as breadstuffs steps, starts at the initial state, chains, and
-- reads `clean`.
#guard
  let tr := noAB.traceFrom noAB.initial clean
  tr.length == clean.length && Bread.traceWord tr == clean &&
    (tr.head?.map (·.state)) == some noAB.initial &&
    (tr.getLast?.map (·.next)) == some (noAB.run clean)

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
