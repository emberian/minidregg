/-
# Pred.Satisfiable — does a law admit ANY step? A witness or a certificate, never a bare claim.

A declared cell's law is a `Pred` over an `(old, new)` pair of `State`s. Its arithmetic atoms
(`eq`, `le`, `memberOf`, `writeOnce`, `monotone`, `eqSlots`, `leSlots`, `leSlotsOff`) are
difference constraints over `Int` slots, possibly guarded by a slot being present or absent
(every atom fails closed on an absent slot). This file decides, for that fragment, whether some
step is admitted, and returns a checked object either way.

## The translation (`Pred.difference?`)

A *node* is the constant `zero`, an old slot or a new slot. A `Sys` is a conjunction of
presence requirements (`present`), absence requirements (`absent`) and difference constraints
`val x ≤ val y + k` (`cons`). `dnf b p` is the list of systems whose union is exactly the set of
steps on which `eval p` returns `b`: negation flips `b`, so it is pushed to the atoms, where each
atom and each negated atom is a short disjunction of systems (a negated inequality is the
opposite inequality shifted by one, which over `Int` is again a difference constraint; a
negated `memberOf` is the union of the gaps between the set's elements). A conjunction is a
product and a disjunction a union. Every intermediate list is checked against `dnfCap`; past it
the translation returns `none` instead of exploding. Products and unions drop every system
another one subsumes (`prune`), and a `memberOf` set becomes one interval per run of consecutive
values, so a law of write-guarded clauses keeps a DNF near its clause count (`guardedEight` has
4 systems, not `4^8`); a conjunction of genuinely independent disjunctions over different slots
still grows exponentially and meets the cap. `sumEq`, `witnessed`, `hashEq` and `ran` are outside the
fragment, so a law containing one returns `none`.

## The decision (`DiffProblem.decide`)

Per system: a node required both present and absent is a `clash`; otherwise Bellman–Ford over
the constraint graph runs `|nodes|` rounds keeping, for every node, the walk that achieved its
distance. If no constraint is violated afterwards, the distances are a potential and give a
candidate step; if one is, the walk through it is searched for a cycle of negative weight.

* A candidate step is returned as `.witness` only after `eval` accepts it on the law itself.
  `witness_sound` is therefore immediate, and makes no claim about Bellman–Ford.
* `.unsat` is returned only when every system carries a certificate that `SysCert.check`
  accepts: a clash, or a list of the system's constraints whose left nodes are a permutation of
  their right nodes and whose bounds sum below zero (summing the inequalities gives `0 < 0`).
  `certificate_unsat` is the real proof: `difference_faithful` (every admitted step satisfies
  one of the systems) plus `SysCert.check_sound`.
* Otherwise `.unknown`. On a translated law that branch is unreachable:
  `Pred.SatisfiableTotal.decide_never_unknown` proves Bellman–Ford always yields a potential or
  a negative cycle, and that each system's step passes `eval`.

Core Lean plus `Pred.Leaf` (for the J13 board-law pole), within the Pred boundary.
-/
import Pred.Leaf

namespace Minidregg.Pred.Sat

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## §1. Nodes, constraints, systems -/

/-- A variable of the constraint graph: the constant `0`, or a slot of the old or new state. -/
inductive Node where
  | zero
  | old (s : Slot)
  | new (s : Slot)
deriving Repr, DecidableEq

/-- What a node reads on a step: `zero` reads `0`; slots read fail-closed. -/
def Node.read (o n : State) : Node → Option Int
  | .zero => some 0
  | .old s => o.get s
  | .new s => n.get s

/-- The value a constraint compares (`0` for an absent slot; the translation only constrains
nodes it also requires present). -/
def Node.val (o n : State) (v : Node) : Int := (v.read o n).getD 0

/-- The difference constraint `val x ≤ val y + k`. -/
structure Con where
  x : Node
  y : Node
  k : Int
deriving Repr, DecidableEq

/-- A conjunctive system: nodes required present, nodes required absent, constraints. -/
structure Sys where
  present : List Node
  absent : List Node
  cons : List Con
deriving Repr, DecidableEq

def Con.Holds (o n : State) (c : Con) : Prop := c.x.val o n ≤ c.y.val o n + c.k

def Sys.Holds (o n : State) (s : Sys) : Prop :=
  (∀ v ∈ s.present, (v.read o n).isSome = true) ∧ (∀ v ∈ s.absent, v.read o n = none) ∧
    ∀ c ∈ s.cons, c.Holds o n

def Sys.top : Sys := ⟨[], [], []⟩

def Sys.merge (a b : Sys) : Sys := ⟨a.present ++ b.present, a.absent ++ b.absent, a.cons ++ b.cons⟩

theorem Sys.holds_top (o n : State) : Sys.top.Holds o n := by
  simp [Sys.Holds, Sys.top]

theorem Sys.holds_merge {o n : State} {a b : Sys} :
    (a.merge b).Holds o n ↔ a.Holds o n ∧ b.Holds o n := by
  simp only [Sys.Holds, Sys.merge, List.mem_append]
  constructor
  · rintro ⟨hp, ha, hc⟩
    exact ⟨⟨fun v h => hp v (.inl h), fun v h => ha v (.inl h), fun c h => hc c (.inl h)⟩,
      ⟨fun v h => hp v (.inr h), fun v h => ha v (.inr h), fun c h => hc c (.inr h)⟩⟩
  · rintro ⟨⟨hp, ha, hc⟩, ⟨hp', ha', hc'⟩⟩
    exact ⟨fun v h => h.elim (hp v) (hp' v), fun v h => h.elim (ha v) (ha' v),
      fun c h => h.elim (hc c) (hc' c)⟩

/-! ## §2. The atoms as systems -/

/-- Present nodes with constraints. -/
def Sys.pres (vs : List Node) (cs : List Con) : Sys := ⟨vs, [], cs⟩
/-- One absent node. -/
def Sys.gone (v : Node) : Sys := ⟨[], [v], []⟩
/-- `val v ≤ c`. -/
def Con.upper (v : Node) (c : Int) : Con := ⟨v, .zero, c⟩
/-- `c ≤ val v`. -/
def Con.lower (v : Node) (c : Int) : Con := ⟨.zero, v, -c⟩

/-- `a` asks for no more than `b`: every requirement of `a` is one of `b`'s, so any step
satisfying `b` satisfies `a`. -/
def Sys.sub (a b : Sys) : Bool :=
  a.present.all (b.present.contains ·) && a.absent.all (b.absent.contains ·) &&
    a.cons.all (b.cons.contains ·)

/-- Add `s` unless a kept system asks for no more; drop the kept systems that ask for more. -/
def pruneStep (acc : List Sys) (s : Sys) : List Sys :=
  if acc.any (fun t => t.sub s) then acc else s :: acc.filter (fun t => !s.sub t)

/-- Drop every system another one subsumes. A law guards each clause to the write verb, and the
guards' branches on one slot multiply across clauses; all but the uniform choices are subsumed,
so pruning keeps a guarded law's DNF near the number of its clauses instead of exponential. -/
def prune (l : List Sys) : List Sys := (l.foldl pruneStep []).reverse

/-- The largest `h' ≥ h` with `h, h+1, …, h'` all in `xs`, searching at most `f` steps. -/
def extendUp (xs : List Int) : Nat → Int → Int
  | 0, h => h
  | f + 1, h => if xs.contains (h + 1) then extendUp xs f (h + 1) else h

/-- The smallest `l ≤ h` with `l, …, h` all in `xs`, searching at most `f` steps. -/
def extendDown (xs : List Int) : Nat → Int → Int
  | 0, h => h
  | f + 1, h => if xs.contains (h - 1) then extendDown xs f (h - 1) else h

namespace Atom
open Sys Con

def eqT (s : Slot) (v : Int) : List Sys := [pres [.new s] [upper (.new s) v, lower (.new s) v]]
def eqF (s : Slot) (v : Int) : List Sys :=
  [gone (.new s), pres [.new s] [upper (.new s) (v - 1)], pres [.new s] [lower (.new s) (v + 1)]]

def leT (s : Slot) (v : Int) : List Sys := [pres [.new s] [upper (.new s) v]]
def leF (s : Slot) (v : Int) : List Sys := [gone (.new s), pres [.new s] [lower (.new s) (v + 1)]]

/-- One interval per run of consecutive elements (`{0,1,2}` is one system, `0 ≤ x ≤ 2`). -/
def memT (s : Slot) (xs : List Int) : List Sys :=
  prune (xs.map fun x => pres [.new s]
    [upper (.new s) (extendUp xs xs.length x), lower (.new s) (extendDown xs xs.length x)])
/-- Strictly below every element, or strictly between an element and every larger one. -/
def memF (s : Slot) (xs : List Int) : List Sys :=
  gone (.new s) :: pres [.new s] (xs.map fun y => upper (.new s) (y - 1)) ::
    xs.map fun x => pres [.new s]
      (lower (.new s) (x + 1) :: (xs.filter fun y => decide (x < y)).map fun y => upper (.new s) (y - 1))

def woT (s : Slot) : List Sys :=
  [gone (.old s), pres [.old s] [upper (.old s) 0, lower (.old s) 0],
   pres [.old s, .new s] [⟨.new s, .old s, 0⟩, ⟨.old s, .new s, 0⟩]]
/-- `old ≠ 0` (two ways) times `new ≠ old` (absent, below, above). -/
def woF (s : Slot) : List Sys :=
  [pres [.old s] [upper (.old s) (-1)], pres [.old s] [lower (.old s) 1]].flatMap fun a =>
    [gone (.new s), pres [.new s] [⟨.new s, .old s, -1⟩], pres [.new s] [⟨.old s, .new s, -1⟩]].map
      a.merge

def monoT (s : Slot) : List Sys := [pres [.old s, .new s] [⟨.old s, .new s, 0⟩]]
def monoF (s : Slot) : List Sys :=
  [gone (.old s), gone (.new s), pres [.old s, .new s] [⟨.new s, .old s, -1⟩]]

def eqsT (a b : Slot) : List Sys := [pres [.new a, .new b] [⟨.new a, .new b, 0⟩, ⟨.new b, .new a, 0⟩]]
def eqsF (a b : Slot) : List Sys :=
  [gone (.new a), gone (.new b), pres [.new a, .new b] [⟨.new a, .new b, -1⟩],
   pres [.new a, .new b] [⟨.new b, .new a, -1⟩]]

def offT (a b : Slot) (k : Int) : List Sys := [pres [.new a, .new b] [⟨.new a, .new b, k⟩]]
def offF (a b : Slot) (k : Int) : List Sys :=
  [gone (.new a), gone (.new b), pres [.new a, .new b] [⟨.new b, .new a, -k - 1⟩]]

end Atom

/-! ## §3. The DNF, capped -/

/-- The most systems any intermediate DNF may hold before pruning; past it the translation says
`none`. -/
def dnfCap : Nat := 1024

def capped (cap : Nat) (l : List Sys) : Option (List Sys) :=
  if l.length ≤ cap then some l else none

def product (cap : Nat) (a b : List Sys) : Option (List Sys) :=
  (capped cap (a.flatMap fun s => b.map s.merge)).map prune

def union (cap : Nat) (a b : List Sys) : Option (List Sys) := (capped cap (a ++ b)).map prune

/-- The atom's systems at polarity `b`, or `none` outside the fragment. -/
def atomDnf (b : Bool) : Pred → Option (List Sys)
  | .eq s v => some (if b then Atom.eqT s v else Atom.eqF s v)
  | .le s v => some (if b then Atom.leT s v else Atom.leF s v)
  | .memberOf s xs => some (if b then Atom.memT s xs else Atom.memF s xs)
  | .writeOnce s => some (if b then Atom.woT s else Atom.woF s)
  | .monotone s => some (if b then Atom.monoT s else Atom.monoF s)
  | .eqSlots x y => some (if b then Atom.eqsT x y else Atom.eqsF x y)
  | .leSlots x y => some (if b then Atom.offT x y 0 else Atom.offF x y 0)
  | .leSlotsOff x y k => some (if b then Atom.offT x y k else Atom.offF x y k)
  | _ => none

mutual
/-- `dnf cap b p`: systems covering every step on which `eval p` is `b`. -/
def dnf (cap : Nat) (b : Bool) (p : Pred) : Option (List Sys) :=
  match p with
  | .not q => dnf cap (!b) q
  | .allL ps => if b then dnfAnd cap b ps else dnfOr cap b ps
  | .anyL ps => if b then dnfOr cap b ps else dnfAnd cap b ps
  | .eq s v => (atomDnf b (.eq s v)).bind (capped cap)
  | .le s v => (atomDnf b (.le s v)).bind (capped cap)
  | .memberOf s xs => (atomDnf b (.memberOf s xs)).bind (capped cap)
  | .writeOnce s => (atomDnf b (.writeOnce s)).bind (capped cap)
  | .monotone s => (atomDnf b (.monotone s)).bind (capped cap)
  | .eqSlots x y => (atomDnf b (.eqSlots x y)).bind (capped cap)
  | .leSlots x y => (atomDnf b (.leSlots x y)).bind (capped cap)
  | .leSlotsOff x y k => (atomDnf b (.leSlotsOff x y k)).bind (capped cap)
  | .sumEq _ _ => none
  | .witnessed _ => none
  | .hashEq _ _ _ => none
  | .ran _ => none
/-- Every child at polarity `b`: a product. -/
def dnfAnd (cap : Nat) (b : Bool) (ps : PredList) : Option (List Sys) :=
  match ps with
  | .nil => some [Sys.top]
  | .cons q rest =>
      match dnf cap b q, dnfAnd cap b rest with
      | some a, some r => product cap a r
      | _, _ => none
/-- Some child at polarity `b`: a union. -/
def dnfOr (cap : Nat) (b : Bool) (ps : PredList) : Option (List Sys) :=
  match ps with
  | .nil => some []
  | .cons q rest =>
      match dnf cap b q, dnfOr cap b rest with
      | some a, some r => union cap a r
      | _, _ => none
end

/-- A law in the fragment, translated: the source law and the systems covering its admitted
steps. -/
structure DiffProblem where
  source : Pred
  systems : List Sys
deriving Repr, DecidableEq

/-- **`Pred.difference?`** — `none` outside the fragment or past `dnfCap`. -/
def _root_.Minidregg.Pred.Pred.difference? (p : Pred) : Option DiffProblem :=
  (dnf dnfCap true p).map fun ss => ⟨p, ss⟩

/-! ## §4. Certificates -/

/-- Why one system has no solution. -/
inductive SysCert where
  /-- A node the system requires both present and absent. -/
  | clash (v : Node)
  /-- Constraints of the system whose left nodes permute their right nodes and whose bounds
  sum below zero: adding them up gives `0 ≤ (negative)`. -/
  | cycle (cs : List Con)
deriving Repr, DecidableEq

/-- One certificate per system, in order. -/
abbrev Certificate := List SysCert

def SysCert.check (s : Sys) : SysCert → Bool
  | .clash v => s.present.contains v && s.absent.contains v
  | .cycle cs =>
      cs.all (fun c => s.cons.contains c) && (cs.map Con.x).isPerm (cs.map Con.y) &&
        decide ((cs.map Con.k).sum < 0)

def checkAll : List Sys → Certificate → Bool
  | [], [] => true
  | s :: ss, c :: cs => c.check s && checkAll ss cs
  | _, _ => false

/-! ## §5. Bellman–Ford with walks -/

def dedupNodes (l : List Node) : List Node :=
  l.foldl (fun acc v => if acc.contains v then acc else acc ++ [v]) []

def Sys.nodes (s : Sys) : List Node :=
  dedupNodes (.zero :: s.present ++ s.cons.flatMap fun c => [c.x, c.y])

/-- Per node: its distance and the walk (latest edge first) that achieved it. -/
abbrev Table := List (Node × Int × List Con)

/-- The first entry for `v`, or distance `0` with the empty walk. -/
def Table.look : Table → Node → Int × List Con
  | [], _ => (0, [])
  | p :: t, v => if p.1 = v then p.2 else Table.look t v

/-- Overwrite every entry for `v`. -/
def Table.set : Table → Node → Int × List Con → Table
  | [], _, _ => []
  | p :: t, v, e => (if p.1 = v then (v, e) else p) :: Table.set t v e

def relax (t : Table) (c : Con) : Table :=
  let ey := t.look c.y
  if ey.1 + c.k < (t.look c.x).1 then t.set c.x (ey.1 + c.k, c :: ey.2) else t

def rounds (cs : List Con) : Nat → Table → Table
  | 0, t => t
  | f + 1, t => rounds cs f (cs.foldl relax t)

/-- The index of the first edge in `acc` whose left node is `v`. -/
def idxOfX (v : Node) : List Con → Option Nat
  | [] => none
  | c :: rest => if c.x == v then some 0 else (idxOfX v rest).map (· + 1)

/-- Split a walk (latest edge first) at its first closed cycle: `(before, cycle, after)`. -/
def splitCycle : List Con → List Con → Option (List Con × List Con × List Con)
  | _, [] => none
  | acc, e :: rest =>
      let acc' := acc ++ [e]
      match idxOfX e.y acc' with
      | some i => some (acc'.take i, acc'.drop i, rest)
      | none => splitCycle acc' rest

/-- Cut cycles out of a walk until one has negative weight. -/
def findNeg : Nat → List Con → Option (List Con)
  | 0, _ => none
  | f + 1, w =>
      match splitCycle [] w with
      | none => none
      | some (pre, cyc, post) =>
          if (cyc.map Con.k).sum < 0 then some cyc else findNeg f (pre ++ post)

/-- What one system comes to. -/
inductive SysOutcome where
  | sat (o n : State)
  | cert (c : SysCert)
  | stuck
deriving Repr, DecidableEq

def stateOf (sel : Node → Option Slot) (val : Node → Int) (vs : List Node) : State :=
  ⟨vs.filterMap fun v => (sel v).map fun s => (s, val v)⟩

def Node.oldSlot : Node → Option Slot
  | .old s => some s
  | _ => none

def Node.newSlot : Node → Option Slot
  | .new s => some s
  | _ => none

def Sys.solve (s : Sys) : SysOutcome :=
  match s.present.find? (fun v => s.absent.contains v) with
  | some v => .cert (.clash v)
  | none =>
      let vs := s.nodes
      let t := rounds s.cons vs.length (vs.map fun v => (v, 0, []))
      match s.cons.find? (fun c => !decide ((t.look c.x).1 ≤ (t.look c.y).1 + c.k)) with
      | none =>
          let val := fun v => (t.look v).1 - (t.look .zero).1
          .sat (stateOf Node.oldSlot val vs) (stateOf Node.newSlot val vs)
      | some c =>
          let w := c :: (t.look c.y).2
          match findNeg (w.length + 1) w with
          | some cyc => .cert (.cycle cyc)
          | none => .stuck

/-! ## §6. The verdict -/

inductive Verdict where
  | witness (o n : State)
  | unsat (cert : Certificate)
  | unknown
deriving Repr, DecidableEq

/-- The first candidate step, from any system, that `eval` accepts on the law. -/
def firstWitness (p : Pred) : List Sys → Option (State × State)
  | [] => none
  | s :: ss =>
      match s.solve with
      | .sat o n => if eval p o n then some (o, n) else firstWitness p ss
      | _ => firstWitness p ss

def certsOf : List Sys → Option Certificate
  | [] => some []
  | s :: ss =>
      match s.solve, certsOf ss with
      | .cert c, some cs => some (c :: cs)
      | _, _ => none

/-- **`DiffProblem.decide`** — a witness `eval` accepted, a certificate `checkAll` accepted, or
`unknown`. -/
def DiffProblem.decide (d : DiffProblem) : Verdict :=
  match firstWitness d.source d.systems with
  | some (o, n) => .witness o n
  | none =>
      match certsOf d.systems with
      | some cs => if checkAll d.systems cs then .unsat cs else .unknown
      | none => .unknown

/-! ## §7. Soundness of a witness: `decide` re-checks it with `eval` -/

theorem firstWitness_eval (p : Pred) :
    ∀ (ss : List Sys) (o n : State), firstWitness p ss = some (o, n) → eval p o n = true
  | [], _, _, h => by simp [firstWitness] at h
  | s :: ss, o, n, h => by
      simp only [firstWitness] at h
      split at h
      · split at h
        · cases h; assumption
        · exact firstWitness_eval p ss o n h
      · exact firstWitness_eval p ss o n h

theorem difference?_source {p : Pred} {d : DiffProblem} (h : p.difference? = some d) :
    d.source = p := by
  simp only [Pred.difference?, Option.map_eq_some_iff] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

/-- **`witness_sound`** — a witness is a step the law admits. Immediate: `decide` returns a
witness only after `eval` accepted it on `d.source`, which is `p`. -/
theorem witness_sound {p : Pred} {d : DiffProblem} {o n : State}
    (hd : p.difference? = some d) (hw : d.decide = .witness o n) : eval p o n = true := by
  rw [← difference?_source hd]
  simp only [DiffProblem.decide] at hw
  split at hw
  · rename_i o' n' h
    cases hw
    exact firstWitness_eval _ _ _ _ h
  · split at hw
    · split at hw <;> cases hw
    · cases hw

/-! ## §8. Soundness of a certificate -/

theorem perm_sum_map {α : Type} (f : α → Int) {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    (l₁.map f).sum = (l₂.map f).sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [List.sum_cons, ih]
  | swap x y l => simp [List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem sum_le_of_holds {o n : State} :
    ∀ cs : List Con, (∀ c ∈ cs, c.Holds o n) →
      (cs.map fun c => c.x.val o n).sum ≤ (cs.map fun c => c.y.val o n).sum + (cs.map Con.k).sum
  | [], _ => by simp
  | c :: cs, h => by
      have hc := h c (List.mem_cons_self ..)
      have ih := sum_le_of_holds cs fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
      simp only [Con.Holds] at hc
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **`SysCert.check_sound`** — a certificate the checker accepts refutes its system. A
clash is a node both present and absent; a cycle sums to `Σ val x ≤ Σ val y + Σ k` with the
two value sums equal (permutation), so `0 ≤ Σ k < 0`. -/
theorem SysCert.check_sound {s : Sys} {c : SysCert} (h : c.check s = true) (o n : State) :
    ¬ s.Holds o n := by
  rintro ⟨hp, ha, hc⟩
  cases c with
  | clash v =>
      simp only [SysCert.check, Bool.and_eq_true, List.contains_iff_mem] at h
      have h1 := hp v h.1
      rw [ha v h.2] at h1
      cases h1
  | cycle cs =>
      simp only [SysCert.check, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
        List.isPerm_iff, decide_eq_true_eq] at h
      obtain ⟨⟨hsub, hperm⟩, hneg⟩ := h
      have hle := sum_le_of_holds (o := o) (n := n) cs fun c hm => hc c (hsub c hm)
      have heq := perm_sum_map (Node.val o n) hperm
      simp only [List.map_map, Function.comp_def] at heq
      omega

theorem checkAll_sound :
    ∀ (ss : List Sys) (cs : Certificate), checkAll ss cs = true →
      ∀ s ∈ ss, ∀ o n, ¬ s.Holds o n
  | [], [], _, _, hs, _, _ => by cases hs
  | s :: ss, c :: cs, h, s', hs', o, n => by
      simp only [checkAll, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hs' with rfl | hs'
      · exact SysCert.check_sound h.1 o n
      · exact checkAll_sound ss cs h.2 s' hs' o n
  | [], _ :: _, h, _, _, _, _ => by simp [checkAll] at h
  | _ :: _, [], h, _, _, _, _ => by simp [checkAll] at h

/-! ## §9. Faithfulness: every step with `eval p = b` satisfies one of `dnf b p`'s systems -/

section Faithful
variable {o n : State}

/-- `∃ s ∈ ss, s.Holds o n`. -/
def Covered (o n : State) (ss : List Sys) : Prop := ∃ s ∈ ss, s.Holds o n

theorem covered_capped {cap : Nat} {l ss : List Sys} (h : capped cap l = some ss)
    (hc : Covered o n l) : Covered o n ss := by
  unfold capped at h; split at h <;> cases h; exact hc

theorem Sys.sub_holds {a b : Sys} (h : a.sub b = true) (hb : b.Holds o n) : a.Holds o n := by
  simp only [Sys.sub, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨hp, ha⟩, hc⟩ := h
  exact ⟨fun v hv => hb.1 v (hp v hv), fun v hv => hb.2.1 v (ha v hv),
    fun c hc' => hb.2.2 c (hc c hc')⟩

theorem Sys.sub_refl (a : Sys) : a.sub a = true := by
  simp [Sys.sub, List.all_eq_true, List.contains_iff_mem]

theorem Sys.sub_trans {a b c : Sys} (h₁ : a.sub b = true) (h₂ : b.sub c = true) :
    a.sub c = true := by
  simp only [Sys.sub, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h₁ h₂ ⊢
  exact ⟨⟨fun v hv => h₂.1.1 v (h₁.1.1 v hv), fun v hv => h₂.1.2 v (h₁.1.2 v hv)⟩,
    fun c' hc => h₂.2 c' (h₁.2 c' hc)⟩

/-- Everything `acc` or `l` held is subsumed by something the fold keeps. -/
theorem foldl_prune_covers :
    ∀ (l acc : List Sys) (s : Sys), (s ∈ acc ∨ s ∈ l) →
      ∃ t ∈ l.foldl pruneStep acc, t.sub s = true
  | [], acc, s, h => ⟨s, by simpa using h, Sys.sub_refl s⟩
  | x :: l, acc, s, h => by
      rw [List.foldl_cons]
      have step : ∀ u, (u ∈ acc ∨ u = x) → ∃ t ∈ pruneStep acc x, t.sub u = true := by
        intro u hu
        unfold pruneStep
        split
        · rename_i hany
          rcases hu with hu | rfl
          · exact ⟨u, hu, Sys.sub_refl u⟩
          · obtain ⟨t, ht, hts⟩ := List.any_eq_true.mp hany
            exact ⟨t, ht, hts⟩
        · rcases hu with hu | rfl
          · by_cases hxu : x.sub u = true
            · exact ⟨x, List.mem_cons_self .., hxu⟩
            · exact ⟨u, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hu, by simpa using hxu⟩),
                Sys.sub_refl u⟩
          · exact ⟨u, List.mem_cons_self .., Sys.sub_refl u⟩
      rcases h with h | h
      · obtain ⟨t, ht, hts⟩ := step s (.inl h)
        obtain ⟨t', ht', hts'⟩ := foldl_prune_covers l (pruneStep acc x) t (.inl ht)
        exact ⟨t', ht', Sys.sub_trans hts' hts⟩
      · rcases List.mem_cons.mp h with rfl | h
        · obtain ⟨t, ht, hts⟩ := step s (.inr rfl)
          obtain ⟨t', ht', hts'⟩ := foldl_prune_covers l (pruneStep acc s) t (.inl ht)
          exact ⟨t', ht', Sys.sub_trans hts' hts⟩
        · exact foldl_prune_covers l (pruneStep acc x) s (.inr h)

theorem covered_prune {l : List Sys} (h : Covered o n l) : Covered o n (prune l) := by
  obtain ⟨s, hs, hh⟩ := h
  obtain ⟨t, ht, hts⟩ := foldl_prune_covers l [] s (.inr hs)
  exact ⟨t, List.mem_reverse.mpr ht, Sys.sub_holds hts hh⟩

theorem covered_product {cap : Nat} {a b ss : List Sys} (h : product cap a b = some ss)
    (ha : Covered o n a) (hb : Covered o n b) : Covered o n ss := by
  unfold product at h
  obtain ⟨raw, hraw, rfl⟩ := Option.map_eq_some_iff.mp h
  apply covered_prune
  apply covered_capped hraw
  obtain ⟨s, hs, hsh⟩ := ha
  obtain ⟨t, ht, hth⟩ := hb
  exact ⟨s.merge t, List.mem_flatMap.mpr ⟨s, hs, List.mem_map.mpr ⟨t, ht, rfl⟩⟩,
    Sys.holds_merge.mpr ⟨hsh, hth⟩⟩

theorem covered_union {cap : Nat} {a b ss : List Sys} (h : union cap a b = some ss)
    (hab : Covered o n a ∨ Covered o n b) : Covered o n ss := by
  unfold union at h
  obtain ⟨raw, hraw, rfl⟩ := Option.map_eq_some_iff.mp h
  apply covered_prune
  apply covered_capped hraw
  rcases hab with ⟨s, hs, hh⟩ | ⟨s, hs, hh⟩
  · exact ⟨s, List.mem_append_left _ hs, hh⟩
  · exact ⟨s, List.mem_append_right _ hs, hh⟩

/-- Membership in a finite set's complement lands in one of `memF`'s gaps. -/
theorem gap_of_not_mem (x : Int) :
    ∀ xs : List Int, x ∉ xs →
      (∀ y ∈ xs, x < y) ∨ ∃ z ∈ xs, z < x ∧ ∀ y ∈ xs, z < y → x < y
  | [], _ => .inl fun _ h => by cases h
  | a :: rest, h => by
      have ha : x ≠ a := fun e => h (e ▸ List.mem_cons_self ..)
      have hr : x ∉ rest := fun m => h (List.mem_cons_of_mem _ m)
      rcases gap_of_not_mem x rest hr with hall | ⟨z, hz, hzx, hzy⟩
      · rcases Int.lt_or_gt_of_ne ha with hlt | hgt
        · refine .inl fun y hy => ?_
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hlt
          · exact hall y hy
        · refine .inr ⟨a, List.mem_cons_self .., hgt, fun y hy hay => ?_⟩
          rcases List.mem_cons.mp hy with rfl | hy
          · omega
          · exact hall y hy
      · rcases Int.lt_or_gt_of_ne ha with hlt | hgt
        · refine .inr ⟨z, List.mem_cons_of_mem _ hz, hzx, fun y hy hzy' => ?_⟩
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hlt
          · exact hzy y hy hzy'
        · by_cases haz : z < a
          · refine .inr ⟨a, List.mem_cons_self .., hgt, fun y hy hay => ?_⟩
            rcases List.mem_cons.mp hy with rfl | hy
            · omega
            · exact hzy y hy (by omega)
          · refine .inr ⟨z, List.mem_cons_of_mem _ hz, hzx, fun y hy hzy' => ?_⟩
            rcases List.mem_cons.mp hy with rfl | hy
            · omega
            · exact hzy y hy hzy'

theorem le_extendUp (xs : List Int) : ∀ (f : Nat) (h : Int), h ≤ extendUp xs f h
  | 0, _ => Int.le_refl _
  | f + 1, h => by
      simp only [extendUp]
      split
      · exact Int.le_trans (Int.le_add_of_nonneg_right (by decide)) (le_extendUp xs f (h + 1))
      · exact Int.le_refl _

theorem extendDown_le (xs : List Int) : ∀ (f : Nat) (h : Int), extendDown xs f h ≤ h
  | 0, _ => Int.le_refl _
  | f + 1, h => by
      simp only [extendDown]
      split
      · have := extendDown_le xs f (h - 1); omega
      · exact Int.le_refl _

theorem memT_covered {s : Slot} {xs : List Int} {x : Int} (hs : n.get s = some x) (hm : x ∈ xs) :
    Covered o n (Atom.memT s xs) := by
  apply covered_prune
  refine ⟨_, List.mem_map.mpr ⟨x, hm, rfl⟩, ?_⟩
  have h1 := le_extendUp xs xs.length x
  have h2 := extendDown_le xs xs.length x
  simp [Sys.Holds, Sys.pres, Con.Holds, Con.upper, Con.lower, Node.val, Node.read, hs]
  omega

theorem memF_covered {s : Slot} {xs : List Int} {x : Int} (hs : n.get s = some x) (hm : x ∉ xs) :
    Covered o n (Atom.memF s xs) := by
  rcases gap_of_not_mem x xs hm with hall | ⟨z, hz, hzx, hzy⟩
  · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
      by simp [Sys.pres, Node.read, hs], by simp [Sys.pres], ?_⟩
    intro c hc
    simp only [Sys.pres, List.mem_map] at hc
    obtain ⟨y, hy, rfl⟩ := hc
    have := hall y hy
    simp [Con.Holds, Con.upper, Node.val, Node.read, hs]; omega
  · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨z, hz, rfl⟩)),
      by simp [Sys.pres, Node.read, hs], by simp [Sys.pres], ?_⟩
    intro c hc
    simp only [Sys.pres, List.mem_cons, List.mem_map, List.mem_filter, decide_eq_true_eq] at hc
    rcases hc with rfl | ⟨y, ⟨hy, hzy'⟩, rfl⟩
    · simp [Con.Holds, Con.lower, Node.val, Node.read, hs]; omega
    · have := hzy y hy hzy'
      simp [Con.Holds, Con.upper, Node.val, Node.read, hs]; omega

/-- The simp set that turns `Covered` of a concrete atom list into arithmetic. -/
macro "atom_simp" : tactic => `(tactic| simp_all [Covered, Atom.eqT, Atom.eqF, Atom.leT, Atom.leF,
  Atom.woT, Atom.woF, Atom.monoT, Atom.monoF, Atom.eqsT, Atom.eqsF, Atom.offT, Atom.offF,
  Sys.merge, Sys.Holds, Sys.pres, Sys.gone, Con.Holds, Con.upper, Con.lower, Node.val, Node.read])

theorem atom_covered (b : Bool) (p : Pred) (ss : List Sys) (h : atomDnf b p = some ss)
    (he : evalWith failClosed p o n = b) : Covered o n ss := by
  cases p with
  | eq s v =>
      simp only [atomDnf, Option.some.injEq] at h; subst h
      simp only [evalWith] at he
      cases hs : n.get s <;> cases b <;> atom_simp <;> omega
  | le s v =>
      simp only [atomDnf, Option.some.injEq] at h; subst h
      simp only [evalWith] at he
      cases hs : n.get s <;> cases b <;> atom_simp <;> omega
  | memberOf s xs =>
      simp only [atomDnf, Option.some.injEq] at h; subst h
      simp only [evalWith] at he
      cases hs : n.get s with
      | none =>
          rw [hs] at he; subst he
          exact ⟨_, List.mem_cons_self .., by simp [Sys.Holds, Sys.gone, Node.read, hs]⟩
      | some x =>
          rw [hs] at he
          dsimp only at he
          cases b with
          | true => exact memT_covered hs (List.contains_iff_mem.mp he)
          | false => exact memF_covered hs fun m => by rw [List.contains_iff_mem.mpr m] at he; cases he
  | writeOnce s =>
      simp only [atomDnf, Option.some.injEq] at h; subst h
      simp only [evalWith] at he
      cases ho : o.get s <;> cases hs : n.get s <;> cases b <;> atom_simp <;> omega
  | monotone s =>
      simp only [atomDnf, Option.some.injEq] at h; subst h
      simp only [evalWith] at he
      cases ho : o.get s <;> cases hs : n.get s <;> cases b <;> atom_simp <;> omega
  | eqSlots x y =>
      simp only [atomDnf, Option.some.injEq] at h; subst h
      simp only [evalWith] at he
      cases hx : n.get x <;> cases hy : n.get y <;> cases b <;> atom_simp <;> omega
  | leSlots x y =>
      simp only [atomDnf, Option.some.injEq] at h; subst h
      simp only [evalWith] at he
      cases hx : n.get x <;> cases hy : n.get y <;> cases b <;> atom_simp <;> omega
  | leSlotsOff x y k =>
      simp only [atomDnf, Option.some.injEq] at h; subst h
      simp only [evalWith] at he
      cases hx : n.get x <;> cases hy : n.get y <;> cases b <;> atom_simp <;> omega
  | sumEq _ _ | witnessed _ | hashEq _ _ _ | ran _ | not _ | allL _ | anyL _ => simp [atomDnf] at h

/-- Every child evaluates to `b`. -/
def AllAre (b : Bool) (o n : State) : PredList → Prop
  | .nil => True
  | .cons q rest => evalWith failClosed q o n = b ∧ AllAre b o n rest

/-- Some child evaluates to `b`. -/
def SomeIs (b : Bool) (o n : State) : PredList → Prop
  | .nil => False
  | .cons q rest => evalWith failClosed q o n = b ∨ SomeIs b o n rest

theorem allAre_true (ps : PredList) (h : evalWithAll failClosed ps o n = true) : AllAre true o n ps := by
  induction ps using PredList.rec' with
  | nil => trivial
  | cons q rest ih =>
      simp only [evalWithAll, Bool.and_eq_true] at h
      exact ⟨h.1, ih h.2⟩

theorem allAre_false (ps : PredList) (h : evalWithAny failClosed ps o n = false) : AllAre false o n ps := by
  induction ps using PredList.rec' with
  | nil => trivial
  | cons q rest ih =>
      simp only [evalWithAny, Bool.or_eq_false_iff] at h
      exact ⟨h.1, ih h.2⟩

theorem someIs_true (ps : PredList) (h : evalWithAny failClosed ps o n = true) : SomeIs true o n ps := by
  induction ps using PredList.rec' with
  | nil => simp [evalWithAny] at h
  | cons q rest ih =>
      simp only [evalWithAny, Bool.or_eq_true] at h
      exact h.elim .inl fun h => .inr (ih h)

theorem someIs_false (ps : PredList) (h : evalWithAll failClosed ps o n = false) : SomeIs false o n ps := by
  induction ps using PredList.rec' with
  | nil => simp [evalWithAll] at h
  | cons q rest ih =>
      simp only [evalWithAll, Bool.and_eq_false_iff] at h
      exact h.elim .inl fun h => .inr (ih h)

mutual
theorem dnf_covers (cap : Nat) :
    (b : Bool) → (p : Pred) → (ss : List Sys) → dnf cap b p = some ss →
      evalWith failClosed p o n = b → Covered o n ss
  | b, .not q, ss, h, he => by
      simp only [dnf] at h
      simp only [evalWith] at he
      exact dnf_covers cap (!b) q ss h (by rw [← he, Bool.not_not])
  | b, .allL ps, ss, h, he => by
      simp only [dnf] at h
      simp only [evalWith] at he
      cases b with
      | true => exact dnfAnd_covers cap true ps ss h (allAre_true ps he)
      | false => exact dnfOr_covers cap false ps ss h (someIs_false ps he)
  | b, .anyL ps, ss, h, he => by
      simp only [dnf] at h
      simp only [evalWith] at he
      cases b with
      | true => exact dnfOr_covers cap true ps ss h (someIs_true ps he)
      | false => exact dnfAnd_covers cap false ps ss h (allAre_false ps he)
  | b, .eq s v, ss, h, he | b, .le s v, ss, h, he | b, .memberOf s v, ss, h, he
  | b, .eqSlots s v, ss, h, he | b, .leSlots s v, ss, h, he => by
      simp only [dnf, Option.bind_eq_some_iff] at h
      obtain ⟨l, hl, hc⟩ := h
      exact covered_capped hc (atom_covered b _ l hl he)
  | b, .writeOnce s, ss, h, he | b, .monotone s, ss, h, he => by
      simp only [dnf, Option.bind_eq_some_iff] at h
      obtain ⟨l, hl, hc⟩ := h
      exact covered_capped hc (atom_covered b _ l hl he)
  | b, .leSlotsOff x y k, ss, h, he => by
      simp only [dnf, Option.bind_eq_some_iff] at h
      obtain ⟨l, hl, hc⟩ := h
      exact covered_capped hc (atom_covered b _ l hl he)
  | _, .sumEq _ _, _, h, _
  | _, .witnessed _, _, h, _ | _, .hashEq _ _ _, _, h, _ | _, .ran _, _, h, _ => by
      simp [dnf] at h
theorem dnfAnd_covers (cap : Nat) :
    (b : Bool) → (ps : PredList) → (ss : List Sys) → dnfAnd cap b ps = some ss →
      AllAre b o n ps → Covered o n ss
  | _, .nil, ss, h, _ => by
      simp only [dnfAnd, Option.some.injEq] at h; subst h
      exact ⟨_, List.mem_singleton_self _, Sys.holds_top o n⟩
  | b, .cons q rest, ss, h, ⟨hq, hr⟩ => by
      simp only [dnfAnd] at h
      split at h
      · rename_i a r ha hrr
        exact covered_product h (dnf_covers cap b q a ha hq) (dnfAnd_covers cap b rest r hrr hr)
      · cases h
theorem dnfOr_covers (cap : Nat) :
    (b : Bool) → (ps : PredList) → (ss : List Sys) → dnfOr cap b ps = some ss →
      SomeIs b o n ps → Covered o n ss
  | _, .nil, _, _, hs => hs.elim
  | b, .cons q rest, ss, h, hs => by
      simp only [dnfOr] at h
      split at h
      · rename_i a r ha hrr
        exact covered_union h (hs.elim (fun hq => .inl (dnf_covers cap b q a ha hq))
          (fun hr => .inr (dnfOr_covers cap b rest r hrr hr)))
      · cases h
end

end Faithful

/-- **`difference_faithful`** — the translation loses no admitted step: every step `eval`
accepts satisfies one of the systems. -/
theorem difference_faithful {p : Pred} {d : DiffProblem} (hd : p.difference? = some d)
    {o n : State} (he : eval p o n = true) : ∃ s ∈ d.systems, s.Holds o n := by
  simp only [Pred.difference?, Option.map_eq_some_iff] at hd
  obtain ⟨ss, hss, rfl⟩ := hd
  exact dnf_covers dnfCap true p ss hss he

theorem decide_unsat_checked {d : DiffProblem} {c : Certificate} (h : d.decide = .unsat c) :
    checkAll d.systems c = true := by
  simp only [DiffProblem.decide] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h; assumption
      · cases h
    · cases h

/-- **`certificate_unsat`** — a law `decide` calls unsatisfiable admits no step at all. -/
theorem certificate_unsat {p : Pred} {d : DiffProblem} {c : Certificate}
    (hd : p.difference? = some d) (hu : d.decide = .unsat c) : ∀ o n, eval p o n = false := by
  intro o n
  cases he : eval p o n with
  | false => rfl
  | true =>
      obtain ⟨s, hs, hh⟩ := difference_faithful hd he
      exact absurd hh (checkAll_sound _ _ (decide_unsat_checked hu) s hs o n)

/-! ## §10. The poles

Each verdict below is computed by the kernel (`rfl`), and each pole is restated as what the
theorems above make of it. -/

namespace Sample

/-- EVAL §2b(b)'s falsifier: `f/1 ≤ 0`, monotone, and `f/1 = 1`. -/
def falsifier : Pred := Pred.all [.le "f/1" 0, .monotone "f/1", .eq "f/1" 1]

/-- The same law without the `eq`. -/
def admitting : Pred := Pred.all [.le "f/1" 0, .monotone "f/1"]

/-- The falsifier's one system carries the certificate `new[f/1] ≤ 0 + 0`, `0 ≤ new[f/1] - 1`:
the left nodes `[new, zero]` permute the right nodes `[zero, new]`, and `0 + (-1) < 0`. -/
theorem falsifier_unsat :
    falsifier.difference?.map DiffProblem.decide =
      some (.unsat [.cycle [⟨.new "f/1", .zero, 0⟩, ⟨.zero, .new "f/1", -1⟩]]) := by
  rfl

/-- The checker has teeth: on the falsifier's system it accepts the real certificate and refuses
an unbalanced one (`new ≤ 0` alone) and an unbalanced one with a negative sum. -/
theorem falsifier_checker_teeth :
    falsifier.difference?.map (fun d => d.systems.map fun s =>
      [(SysCert.cycle [⟨.new "f/1", .zero, 0⟩, ⟨.zero, .new "f/1", -1⟩]).check s,
       (SysCert.cycle [⟨.new "f/1", .zero, 0⟩]).check s,
       (SysCert.cycle [⟨.zero, .new "f/1", -1⟩]).check s,
       (SysCert.clash (.new "f/1")).check s]) =
      some [[true, false, false, false]] := by
  rfl

theorem falsifier_admits_nothing : ∀ o n, eval falsifier o n = false := by
  cases h : falsifier.difference? with
  | none =>
      have hu := falsifier_unsat
      rw [h] at hu
      cases hu
  | some d =>
      have hu := falsifier_unsat
      rw [h] at hu
      exact certificate_unsat h (Option.some.inj hu)

/-- Dropping the `eq` gives a witness: `f/1` is `0` before and after. -/
theorem admitting_witness :
    admitting.difference?.map DiffProblem.decide =
      some (.witness ⟨[("f/1", 0)]⟩ ⟨[("f/1", 0)]⟩) := by
  rfl

/-- `eval` accepts that witness. -/
theorem admitting_witness_admitted : eval admitting ⟨[("f/1", 0)]⟩ ⟨[("f/1", 0)]⟩ = true := by
  decide

/-- P-LAW's `sealed` (`any []`, `Pred.Leaf.LeafSample.sealed_names_itself`), decided: it has
no system, so its certificate is the empty list. -/
theorem sealed_decided :
    (Pred.any []).difference?.map DiffProblem.decide = some (.unsat []) := by
  rfl

theorem sealed_admits_nothing : ∀ o n, eval (Pred.any []) o n = false :=
  certificate_unsat (d := ⟨Pred.any [], []⟩) (c := []) rfl rfl

/-- `not open` is decided the same way. -/
theorem not_open_decided :
    (Pred.not (Pred.all [])).difference?.map DiffProblem.decide = some (.unsat []) := by
  rfl

/-- One system clashes (`f/1` both equal to `0` and absent), the other is a cycle
(`f/1 = 0` against `f/1 ≥ 6`). -/
theorem clash_unsat :
    (Pred.all [.eq "f/1" 0, .not (.le "f/1" 5), .monotone "f/1"]).difference?.map
      DiffProblem.decide = some (.unsat [.clash (.new "f/1"),
        .cycle [⟨.new "f/1", .zero, 0⟩, ⟨.zero, .new "f/1", -6⟩]]) := by
  rfl

/-- J13's board law (`Pred.Leaf.LeafSample.boardLaw`) has a witness: `field 2` stays `0` on a
step that is not a write. -/
theorem boardLaw_witness :
    LeafSample.boardLaw.difference?.map DiffProblem.decide =
      some (.witness ⟨[("resource/field/2/after", 0)]⟩ ⟨[("resource/field/2/after", 0)]⟩) := by
  rfl

/-- Eight write-guarded clauses on eight slots. Unpruned, the guards' branches multiply to
`4^8` systems; subsumption keeps the three uniform guard choices and the one where every clause
holds. -/
def guardedEight : Pred :=
  Pred.all (["f/0", "f/1", "f/2", "f/3", "f/4", "f/5", "f/6", "f/7"].map fun s =>
    LeafSample.onWrite (.monotone s))

theorem guardedEight_four_systems : guardedEight.difference?.map (·.systems.length) = some 4 := by
  rfl

/-- A run of consecutive values is one interval: `f/1 ∈ {0, 1, 2, 7}` is two systems. -/
theorem memberOf_runs :
    (Pred.memberOf "f/1" [0, 1, 2, 7]).difference?.map (·.systems.length) = some 2 := by
  rfl

/-- A law outside the fragment: a third-party claim. -/
theorem witnessed_outside :
    (Pred.all [.le "f/1" 0, .witnessed ⟨"vk-1"⟩]).difference? = none := by
  rfl

end Sample

end Minidregg.Pred.Sat

/-- info: 'Minidregg.Pred.Sat.witness_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Minidregg.Pred.Sat.witness_sound
/-- info: 'Minidregg.Pred.Sat.certificate_unsat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Minidregg.Pred.Sat.certificate_unsat
/-- info: 'Minidregg.Pred.Sat.difference_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Minidregg.Pred.Sat.difference_faithful
/-- info: 'Minidregg.Pred.Sat.Sample.falsifier_admits_nothing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Minidregg.Pred.Sat.Sample.falsifier_admits_nothing
