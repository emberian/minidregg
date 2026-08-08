/-
# `Compiler/AirFlatten.lean` — [AIR-flatten]: nested expressions → bounded-degree gate systems, DERIVED

**Substrate, said out loud:** this is Lean-authored arithmetization. The flattening of a nested
`Term (AirSig F Idx)` into a degree-≤2 GATE SYSTEM with auxiliary wires is a FOLD
(`flatten = fold flattenAlg` — the derived path, never a hand-authored Rust AIR), and its
semantic preservation is PROVED here as the wire-forcing refinement: every gate pins its output
wire to the value of its node, so any assignment of the aux wires that satisfies the gates is
FORCED to the executor's intermediate values, and the root wire is forced to `eval asg t`.
Chained through `accepts_iff_semHolds` (Compiler/Air §3), the flattened system's satisfiability
IS the executor relation — the deployment-shaped arithmetization (R1CS/Plonkish gates, not one
big polynomial) with the same drift-impossibility as rung 1.

## The construction

* A `WireRef` is a constant, an original variable, or an aux wire (a `ℕ` allocated fresh).
* A `Gate` is `a ⋄ b = out` with `⋄ ∈ {+, ·}` and `out` an aux wire — degree ≤ 2 by shape:
  one binary field operation on two wire reads, equated to a wire read. No gate ever nests.
* `flattenAlg` is an `Alg (AirSig F Idx)` on the state-threading carrier
  `ℕ → FlatOut` (fresh-counter in; output wire, gate list, new counter out): `const`/`var`
  return their ref and no gates; `add`/`mul` flatten left then right, allocate ONE fresh aux
  wire, and emit ONE gate. `flatten := fold flattenAlg` — the catamorphism, on the nose.

## The refinement (what is PROVED, and in which direction)

* `flatten_forces` — **wire-forcing, the sound direction**: for ANY aux valuation satisfying
  every emitted gate, the root output wire reads `eval asg t`. No freshness hypothesis needed:
  gates only ever constrain, so a satisfying valuation is already forced. One induction.
* `flatten_scoped` — the freshness invariant: every aux wire mentioned lives in
  `[n₀, next)`, gate inputs mention only wires strictly below their own output wire, and the
  counter is monotone. One induction, conjunctive.
* `flatten_sound` — **the forced extension exists (completeness)**: some aux valuation
  satisfies every gate AND reads the root as `eval asg t` — built by merging the sub-extensions
  along the scoping invariant (fresh wires do not collide) and forcing the new wire.
* `flatten_constraint_iff` — the keystone: the gate system + root-wire-zero is satisfiable
  iff `accepts asg t` iff `semHolds asg t` (the executor relation) — the full chain
  gate system ⟺ circuit ⟺ executor, closed.

* `flatten_covers` + `flatten_aux_unique` — **the forced extension is UNIQUE**: every
  allocated wire is some gate's output, inputs sit strictly below outputs, so any two
  satisfying valuations agree on the whole allocated range. `[AIR-flatten-fresh]` (fresh-wire
  non-collision bookkeeping) is thereby CLOSED, not residual.

Honest scope: degree-≤2 is BY SHAPE of `Gate` (one binary field op on two wire reads, equated
to one wire read — gates cannot nest), not a numeric degree function; the refinement theorems
are inductions over the SAME signature the fold consumes (`flatten_forces`, `flatten_scoped`,
`flatten_sound`, `flatten_covers` — one induction each), with the gate system itself produced
ONLY by the fold. Residuals that remain live upstream, unchanged: `[AIR-sumcheck]` (retire the
gate constraints through `Loom/SumcheckReduction`), `[AIR-poseidon]`/`[AIR-membership]` (the
note-spend gadgets, grown on this rung).
-/
import Compiler.Air

namespace Minidregg.Compiler

universe u

variable {F : Type u} [Field F] {Idx : Type u}

/-! ## §1. Wires and gates — the degree-≤2 target vocabulary. -/

/-- A wire reference: a literal constant, an original variable of the expression, or an
auxiliary wire allocated by the flattener. -/
inductive WireRef (F : Type u) (Idx : Type u)
  | cnst (c : F)
  | var (i : Idx)
  | aux (n : ℕ)

/-- Read a wire under a variable assignment and an aux-wire valuation. -/
def WireRef.read (asg : Idx → F) (auxv : ℕ → F) : WireRef F Idx → F
  | .cnst c => c
  | .var i => asg i
  | .aux n => auxv n

/-- The two gate operations. -/
inductive GateOp
  | add
  | mul
deriving DecidableEq

/-- Gate-op denotation into the field. -/
def GateOp.denote : GateOp → F → F → F
  | .add => (· + ·)
  | .mul => (· * ·)

/-- **A gate**: `a ⋄ b = out`, with `out` always an aux wire. Degree ≤ 2 by construction —
one binary operation on two wire reads equated to a wire read; gates never nest. -/
structure Gate (F : Type u) (Idx : Type u) where
  op : GateOp
  a : WireRef F Idx
  b : WireRef F Idx
  out : ℕ

omit [Field F] in
@[simp] theorem WireRef.read_cnst (asg : Idx → F) (auxv : ℕ → F) (c : F) :
    (WireRef.cnst c : WireRef F Idx).read asg auxv = c := rfl

omit [Field F] in
@[simp] theorem WireRef.read_var (asg : Idx → F) (auxv : ℕ → F) (i : Idx) :
    (WireRef.var i : WireRef F Idx).read asg auxv = asg i := rfl

omit [Field F] in
@[simp] theorem WireRef.read_aux (asg : Idx → F) (auxv : ℕ → F) (n : ℕ) :
    (WireRef.aux n : WireRef F Idx).read asg auxv = auxv n := rfl

/-- A gate HOLDS under `(asg, auxv)` when its operation applied to its input reads equals its
output wire's value. -/
def Gate.holds (asg : Idx → F) (auxv : ℕ → F) (g : Gate F Idx) : Prop :=
  g.op.denote (g.a.read asg auxv) (g.b.read asg auxv) = auxv g.out

/-- The whole emitted system holds. -/
def gatesHold (asg : Idx → F) (auxv : ℕ → F) (gs : List (Gate F Idx)) : Prop :=
  ∀ g ∈ gs, g.holds asg auxv

/-! ## §2. The flattening — a genuine fold into a state-threading carrier. -/

/-- Result of flattening one node: its output wire, the gates emitted so far (in allocation
order), and the next fresh aux index. -/
structure FlatOut (F : Type u) (Idx : Type u) where
  out : WireRef F Idx
  gates : List (Gate F Idx)
  next : ℕ

/-- The flattening carrier: fresh-counter in, `FlatOut` out. The fresh-wire state is threaded
EXPLICITLY through a function carrier so the flattening stays a genuine catamorphism. -/
abbrev Flat (F : Type u) (Idx : Type u) : Type u := ℕ → FlatOut F Idx

/-- **The flattening algebra** — the derived path: leaves return their ref with no gates;
`add`/`mul` flatten left then right, allocate one fresh aux wire, emit one gate. -/
def flattenAlg : Alg (AirSig F Idx) (Flat F Idx) := fun s =>
  match s with
  | .const c => fun _ n => ⟨.cnst c, [], n⟩
  | .var i => fun _ n => ⟨.var i, [], n⟩
  | .add => fun k n =>
      let l := k false n
      let r := k true l.next
      ⟨.aux r.next, l.gates ++ r.gates ++ [⟨.add, l.out, r.out, r.next⟩], r.next + 1⟩
  | .mul => fun k n =>
      let l := k false n
      let r := k true l.next
      ⟨.aux r.next, l.gates ++ r.gates ++ [⟨.mul, l.out, r.out, r.next⟩], r.next + 1⟩

/-- **The flattening** — the fold of `flattenAlg`. NOT hand-recursed: the gate system comes
out of the one catamorphism, so the derived-path law applies verbatim. -/
def flatten : Term (AirSig F Idx) → Flat F Idx :=
  fold flattenAlg

omit [Field F] in
/-- Computation rule on the DSL surface constructors (all definitional). -/
@[simp] theorem flatten_cst (c : F) (n : ℕ) :
    flatten (cst c (Idx := Idx)) n = ⟨.cnst c, [], n⟩ := rfl

omit [Field F] in
@[simp] theorem flatten_vr (i : Idx) (n : ℕ) :
    flatten (vr i (F := F)) n = ⟨.var i, [], n⟩ := rfl

omit [Field F] in
@[simp] theorem flatten_add' (a b : Term (AirSig F Idx)) (n : ℕ) :
    flatten (add' a b) n =
      let l := flatten a n
      let r := flatten b l.next
      ⟨.aux r.next, l.gates ++ r.gates ++ [⟨.add, l.out, r.out, r.next⟩], r.next + 1⟩ := rfl

omit [Field F] in
@[simp] theorem flatten_mul' (a b : Term (AirSig F Idx)) (n : ℕ) :
    flatten (mul' a b) n =
      let l := flatten a n
      let r := flatten b l.next
      ⟨.aux r.next, l.gates ++ r.gates ++ [⟨.mul, l.out, r.out, r.next⟩], r.next + 1⟩ := rfl

omit [Field F] in
/-- Computation rule in raw `.mk` form (what the induction cases see). -/
theorem flatten_mk_add (k : Bool → Term (AirSig F Idx)) (n : ℕ) :
    flatten (.mk .add k) n =
      let l := flatten (k false) n
      let r := flatten (k true) l.next
      ⟨.aux r.next, l.gates ++ r.gates ++ [⟨.add, l.out, r.out, r.next⟩], r.next + 1⟩ := rfl

omit [Field F] in
theorem flatten_mk_mul (k : Bool → Term (AirSig F Idx)) (n : ℕ) :
    flatten (.mk .mul k) n =
      let l := flatten (k false) n
      let r := flatten (k true) l.next
      ⟨.aux r.next, l.gates ++ r.gates ++ [⟨.mul, l.out, r.out, r.next⟩], r.next + 1⟩ := rfl

/-! ## §3. `flatten_forces` — wire-forcing, the sound direction.

ANY aux valuation that satisfies every emitted gate reads the root output wire as
`eval asg t`. No freshness hypothesis: gates only constrain, so wherever a satisfying
valuation exists it is already forced through the gate chain to the executor's values.
This is the direction the constraint chain consumes (a satisfying witness cannot lie
about the root), and it is proved OUTRIGHT — one induction, no residual. -/

/-- **Wire-forcing**: if every gate of `flatten t n₀` holds under `(asg, auxv)`, the root
output wire reads exactly `eval asg t` — each aux wire in the spine is FORCED to its node's
intermediate value, so the gate system cannot accept a wrong root. -/
theorem flatten_forces (asg : Idx → F) (t : Term (AirSig F Idx)) (n₀ : ℕ) (auxv : ℕ → F)
    (h : gatesHold asg auxv (flatten t n₀).gates) :
    (flatten t n₀).out.read asg auxv = eval asg t := by
  induction t generalizing n₀ with
  | mk s k ih =>
    cases s with
    | const c => rfl
    | var i => rfl
    | add =>
      have hl : gatesHold asg auxv (flatten (k false) n₀).gates := fun g hg =>
        h g (List.mem_append_left _ (List.mem_append_left _ hg))
      have hr : gatesHold asg auxv
          (flatten (k true) (flatten (k false) n₀).next).gates := fun g hg =>
        h g (List.mem_append_left _ (List.mem_append_right _ hg))
      have hgate : Gate.holds asg auxv
          ⟨.add, (flatten (k false) n₀).out,
            (flatten (k true) (flatten (k false) n₀).next).out,
            (flatten (k true) (flatten (k false) n₀).next).next⟩ :=
        h _ (List.mem_append_right _ (List.mem_singleton_self _))
      have el := ih false n₀ hl
      have er := ih true (flatten (k false) n₀).next hr
      show auxv (flatten (k true) (flatten (k false) n₀).next).next
          = eval asg (k false) + eval asg (k true)
      rw [← el, ← er]
      exact hgate.symm
    | mul =>
      have hl : gatesHold asg auxv (flatten (k false) n₀).gates := fun g hg =>
        h g (List.mem_append_left _ (List.mem_append_left _ hg))
      have hr : gatesHold asg auxv
          (flatten (k true) (flatten (k false) n₀).next).gates := fun g hg =>
        h g (List.mem_append_left _ (List.mem_append_right _ hg))
      have hgate : Gate.holds asg auxv
          ⟨.mul, (flatten (k false) n₀).out,
            (flatten (k true) (flatten (k false) n₀).next).out,
            (flatten (k true) (flatten (k false) n₀).next).next⟩ :=
        h _ (List.mem_append_right _ (List.mem_singleton_self _))
      have el := ih false n₀ hl
      have er := ih true (flatten (k false) n₀).next hr
      show auxv (flatten (k true) (flatten (k false) n₀).next).next
          = eval asg (k false) * eval asg (k true)
      rw [← el, ← er]
      exact hgate.symm

/-! ## §4. The freshness invariant — `flatten_scoped`.

Every aux wire the flattening of `t` at counter `n₀` MENTIONS lives in the allocated range
`[n₀, next)`; gate inputs mention only wires strictly below their own output; the counter is
monotone. This is the non-collision bookkeeping that lets sub-extensions merge in
`flatten_sound` — proved outright, one conjunctive induction. -/

/-- `w.auxIn lo hi`: if `w` is an aux wire, its index lies in `[lo, hi)`. Constants and
original variables are unconstrained (they are not allocated). -/
def WireRef.auxIn (lo hi : ℕ) : WireRef F Idx → Prop
  | .aux n => lo ≤ n ∧ n < hi
  | _ => True

omit [Field F] in
theorem WireRef.auxIn_mono {lo hi lo' hi' : ℕ} (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    {w : WireRef F Idx} (h : w.auxIn lo hi) : w.auxIn lo' hi' := by
  cases w with
  | aux n => exact ⟨hlo.trans h.1, h.2.trans_le hhi⟩
  | cnst c => trivial
  | var i => trivial

/-- A gate is SCOPED in `[lo, hi)`: its output wire is allocated in the range, and its inputs
mention only aux wires allocated strictly EARLIER than its output (`[lo, g.out)`) — the
acyclicity that makes each gate genuinely FORCE its output from already-determined wires. -/
def Gate.scopedIn (lo hi : ℕ) (g : Gate F Idx) : Prop :=
  g.a.auxIn lo g.out ∧ g.b.auxIn lo g.out ∧ lo ≤ g.out ∧ g.out < hi

omit [Field F] in
theorem Gate.scopedIn_mono {lo hi lo' hi' : ℕ} (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    {g : Gate F Idx} (h : g.scopedIn lo hi) : g.scopedIn lo' hi' :=
  ⟨WireRef.auxIn_mono hlo le_rfl h.1, WireRef.auxIn_mono hlo le_rfl h.2.1,
    hlo.trans h.2.2.1, h.2.2.2.trans_le hhi⟩

omit [Field F] in
/-- **The freshness invariant**: the counter is monotone, the root output wire is either
unallocated (const/var) or in-range, and every emitted gate is scoped — inputs strictly below
their own output, output in `[n₀, next)`. Fresh wires never collide across subtrees. -/
theorem flatten_scoped (t : Term (AirSig F Idx)) (n₀ : ℕ) :
    n₀ ≤ (flatten t n₀).next ∧
      (flatten t n₀).out.auxIn n₀ (flatten t n₀).next ∧
      ∀ g ∈ (flatten t n₀).gates, g.scopedIn n₀ (flatten t n₀).next := by
  induction t generalizing n₀ with
  | mk s k ih =>
    cases s with
    | const c => exact ⟨le_rfl, trivial, fun g hg => nomatch hg⟩
    | var i => exact ⟨le_rfl, trivial, fun g hg => nomatch hg⟩
    | add =>
      obtain ⟨hn₁, _, hgl⟩ := ih false n₀
      obtain ⟨hn₂, _, hgr⟩ := ih true (flatten (k false) n₀).next
      obtain ⟨_, hol, _⟩ := ih false n₀
      obtain ⟨_, hor, _⟩ := ih true (flatten (k false) n₀).next
      simp only [flatten_mk_add]
      refine ⟨by omega, ⟨by omega, by omega⟩, ?_⟩
      intro g hg
      rcases List.mem_append.mp hg with hg' | hg'
      · rcases List.mem_append.mp hg' with hgm | hgm
        · exact Gate.scopedIn_mono le_rfl (by omega) (hgl g hgm)
        · exact Gate.scopedIn_mono hn₁ (by omega) (hgr g hgm)
      · rw [List.mem_singleton.mp hg']
        refine ⟨WireRef.auxIn_mono le_rfl hn₂ hol,
          WireRef.auxIn_mono hn₁ le_rfl hor, ?_, ?_⟩
        · show n₀ ≤ (flatten (k true) (flatten (k false) n₀).next).next
          omega
        · show (flatten (k true) (flatten (k false) n₀).next).next
              < (flatten (k true) (flatten (k false) n₀).next).next + 1
          omega
    | mul =>
      obtain ⟨hn₁, _, hgl⟩ := ih false n₀
      obtain ⟨hn₂, _, hgr⟩ := ih true (flatten (k false) n₀).next
      obtain ⟨_, hol, _⟩ := ih false n₀
      obtain ⟨_, hor, _⟩ := ih true (flatten (k false) n₀).next
      simp only [flatten_mk_mul]
      refine ⟨by omega, ⟨by omega, by omega⟩, ?_⟩
      intro g hg
      rcases List.mem_append.mp hg with hg' | hg'
      · rcases List.mem_append.mp hg' with hgm | hgm
        · exact Gate.scopedIn_mono le_rfl (by omega) (hgl g hgm)
        · exact Gate.scopedIn_mono hn₁ (by omega) (hgr g hgm)
      · rw [List.mem_singleton.mp hg']
        refine ⟨WireRef.auxIn_mono le_rfl hn₂ hol,
          WireRef.auxIn_mono hn₁ le_rfl hor, ?_, ?_⟩
        · show n₀ ≤ (flatten (k true) (flatten (k false) n₀).next).next
          omega
        · show (flatten (k true) (flatten (k false) n₀).next).next
              < (flatten (k true) (flatten (k false) n₀).next).next + 1
          omega

/-! ## §5. Congruence — reads and gates only see the aux wires they mention. -/

omit [Field F] in
/-- A wire read only depends on the aux valuation inside the wire's range. -/
theorem WireRef.read_congr {asg : Idx → F} {auxv auxv' : ℕ → F} {lo hi : ℕ}
    (hagree : ∀ m, lo ≤ m → m < hi → auxv m = auxv' m)
    {w : WireRef F Idx} (hw : w.auxIn lo hi) :
    w.read asg auxv = w.read asg auxv' := by
  cases w with
  | cnst c => rfl
  | var i => rfl
  | aux n => exact hagree n hw.1 hw.2

/-- A scoped gate's satisfaction transfers along any aux valuation agreeing on its scope. -/
theorem Gate.holds_congr {asg : Idx → F} {auxv auxv' : ℕ → F} {lo hi : ℕ}
    (hagree : ∀ m, lo ≤ m → m < hi → auxv m = auxv' m)
    {g : Gate F Idx} (hs : g.scopedIn lo hi) (h : g.holds asg auxv) :
    g.holds asg auxv' := by
  obtain ⟨ha, hb, hlo, hhi⟩ := hs
  unfold Gate.holds at h ⊢
  rw [← WireRef.read_congr hagree (WireRef.auxIn_mono le_rfl hhi.le ha),
    ← WireRef.read_congr hagree (WireRef.auxIn_mono le_rfl hhi.le hb),
    ← hagree g.out hlo hhi]
  exact h

/-! ## §6. `flatten_sound` — the forced extension EXISTS (completeness).

Given only the var-assignment, the aux wires can be extended by the FORCED values (each aux
wire takes its node's intermediate `eval`) so that every emitted gate holds and the root wire
reads `eval asg t`. Built by merging the sub-extensions — legal precisely because
`flatten_scoped` says the subtrees' fresh wires never collide. -/

/-- **`flatten_sound`** — the forced aux extension: some valuation of the aux wires satisfies
EVERY emitted gate, and under it the root output wire reads exactly `eval asg t`. Together with
`flatten_forces` this is the wire-forcing refinement: a satisfying extension exists, and every
satisfying extension agrees at the root. -/
theorem flatten_sound (asg : Idx → F) (t : Term (AirSig F Idx)) (n₀ : ℕ) :
    ∃ auxv : ℕ → F, gatesHold asg auxv (flatten t n₀).gates ∧
      (flatten t n₀).out.read asg auxv = eval asg t := by
  induction t generalizing n₀ with
  | mk s k ih =>
    cases s with
    | const c =>
      refine ⟨fun _ => 0, ?_, rfl⟩
      intro g hg
      exact nomatch hg
    | var i =>
      refine ⟨fun _ => 0, ?_, rfl⟩
      intro g hg
      exact nomatch hg
    | add =>
      obtain ⟨auxv₁, hg₁, ho₁⟩ := ih false n₀
      obtain ⟨auxv₂, hg₂, ho₂⟩ := ih true (flatten (k false) n₀).next
      obtain ⟨hle₁, hol, hsl⟩ := flatten_scoped (k false) n₀
      obtain ⟨hle₂, hor, hsr⟩ := flatten_scoped (k true) (flatten (k false) n₀).next
      simp only [flatten_mk_add]
      set n₁ := (flatten (k false) n₀).next with hn₁
      set n₂ := (flatten (k true) n₁).next with hn₂
      set v : ℕ → F := fun m => if m < n₁ then auxv₁ m else if m < n₂ then auxv₂ m
        else eval asg (k false) + eval asg (k true) with hv
      have hA1 : ∀ m, n₀ ≤ m → m < n₁ → auxv₁ m = v m := fun m _ hm => by
        simp only [hv]; rw [if_pos hm]
      have hA2 : ∀ m, n₁ ≤ m → m < n₂ → auxv₂ m = v m := fun m hm hm' => by
        simp only [hv]; rw [if_neg (by omega), if_pos hm']
      have hvn₂ : v n₂ = eval asg (k false) + eval asg (k true) := by
        simp only [hv]; rw [if_neg (by omega), if_neg (by omega)]
      refine ⟨v, ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with hg' | hg'
        · rcases List.mem_append.mp hg' with hgm | hgm
          · exact Gate.holds_congr hA1 (hsl g hgm) (hg₁ g hgm)
          · exact Gate.holds_congr hA2 (hsr g hgm) (hg₂ g hgm)
        · rw [List.mem_singleton.mp hg']
          show GateOp.denote .add ((flatten (k false) n₀).out.read asg v)
            ((flatten (k true) n₁).out.read asg v) = v n₂
          rw [← WireRef.read_congr hA1 hol, ← WireRef.read_congr hA2 hor, ho₁, ho₂, hvn₂]
          rfl
      · show (WireRef.aux n₂).read asg v = eval asg (.mk .add k)
        rw [WireRef.read_aux, hvn₂]
        rfl
    | mul =>
      obtain ⟨auxv₁, hg₁, ho₁⟩ := ih false n₀
      obtain ⟨auxv₂, hg₂, ho₂⟩ := ih true (flatten (k false) n₀).next
      obtain ⟨hle₁, hol, hsl⟩ := flatten_scoped (k false) n₀
      obtain ⟨hle₂, hor, hsr⟩ := flatten_scoped (k true) (flatten (k false) n₀).next
      simp only [flatten_mk_mul]
      set n₁ := (flatten (k false) n₀).next with hn₁
      set n₂ := (flatten (k true) n₁).next with hn₂
      set v : ℕ → F := fun m => if m < n₁ then auxv₁ m else if m < n₂ then auxv₂ m
        else eval asg (k false) * eval asg (k true) with hv
      have hA1 : ∀ m, n₀ ≤ m → m < n₁ → auxv₁ m = v m := fun m _ hm => by
        simp only [hv]; rw [if_pos hm]
      have hA2 : ∀ m, n₁ ≤ m → m < n₂ → auxv₂ m = v m := fun m hm hm' => by
        simp only [hv]; rw [if_neg (by omega), if_pos hm']
      have hvn₂ : v n₂ = eval asg (k false) * eval asg (k true) := by
        simp only [hv]; rw [if_neg (by omega), if_neg (by omega)]
      refine ⟨v, ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with hg' | hg'
        · rcases List.mem_append.mp hg' with hgm | hgm
          · exact Gate.holds_congr hA1 (hsl g hgm) (hg₁ g hgm)
          · exact Gate.holds_congr hA2 (hsr g hgm) (hg₂ g hgm)
        · rw [List.mem_singleton.mp hg']
          show GateOp.denote .mul ((flatten (k false) n₀).out.read asg v)
            ((flatten (k true) n₁).out.read asg v) = v n₂
          rw [← WireRef.read_congr hA1 hol, ← WireRef.read_congr hA2 hor, ho₁, ho₂, hvn₂]
          rfl
      · show (WireRef.aux n₂).read asg v = eval asg (.mk .mul k)
        rw [WireRef.read_aux, hvn₂]
        rfl

/-! ## §7. The forced extension is UNIQUE on the allocated range.

Every allocated wire is some gate's output (`flatten_covers`), and every gate's inputs sit
strictly below its output (`flatten_scoped`), so the gates form a well-founded chain: two
satisfying valuations agree on EVERY allocated aux wire, by strong induction on the wire
index. This closes the fresh-wire bookkeeping outright — "each aux is FORCED" is a theorem,
not a residual. -/

omit [Field F] in
/-- **Coverage**: every aux index in the allocated range `[n₀, next)` is the output wire of
some emitted gate — no dangling allocations. -/
theorem flatten_covers (t : Term (AirSig F Idx)) (n₀ : ℕ) :
    ∀ m, n₀ ≤ m → m < (flatten t n₀).next →
      ∃ g ∈ (flatten t n₀).gates, g.out = m := by
  induction t generalizing n₀ with
  | mk s k ih =>
    cases s with
    | const c =>
      intro m h₁ h₂
      have hnext : (flatten (WType.mk (AirOp.const c) k) n₀).next = n₀ := rfl
      omega
    | var i =>
      intro m h₁ h₂
      have hnext : (flatten (WType.mk (AirOp.var i) k) n₀).next = n₀ := rfl
      omega
    | add =>
      obtain ⟨hle₁, -, -⟩ := flatten_scoped (k false) n₀
      obtain ⟨hle₂, -, -⟩ := flatten_scoped (k true) (flatten (k false) n₀).next
      simp only [flatten_mk_add]
      intro m h₁ h₂
      by_cases hm₁ : m < (flatten (k false) n₀).next
      · obtain ⟨g, hg, hgo⟩ := ih false n₀ m h₁ hm₁
        exact ⟨g, List.mem_append_left _ (List.mem_append_left _ hg), hgo⟩
      · by_cases hm₂ : m < (flatten (k true) (flatten (k false) n₀).next).next
        · obtain ⟨g, hg, hgo⟩ := ih true (flatten (k false) n₀).next m (by omega) hm₂
          exact ⟨g, List.mem_append_left _ (List.mem_append_right _ hg), hgo⟩
        · refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
          show (flatten (k true) (flatten (k false) n₀).next).next = m
          omega
    | mul =>
      obtain ⟨hle₁, -, -⟩ := flatten_scoped (k false) n₀
      obtain ⟨hle₂, -, -⟩ := flatten_scoped (k true) (flatten (k false) n₀).next
      simp only [flatten_mk_mul]
      intro m h₁ h₂
      by_cases hm₁ : m < (flatten (k false) n₀).next
      · obtain ⟨g, hg, hgo⟩ := ih false n₀ m h₁ hm₁
        exact ⟨g, List.mem_append_left _ (List.mem_append_left _ hg), hgo⟩
      · by_cases hm₂ : m < (flatten (k true) (flatten (k false) n₀).next).next
        · obtain ⟨g, hg, hgo⟩ := ih true (flatten (k false) n₀).next m (by omega) hm₂
          exact ⟨g, List.mem_append_left _ (List.mem_append_right _ hg), hgo⟩
        · refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
          show (flatten (k true) (flatten (k false) n₀).next).next = m
          omega

/-- **Per-wire uniqueness — the aux wires are FORCED.** Any two aux valuations satisfying
every emitted gate agree on EVERY wire in the allocated range: each allocated wire is a gate
output (`flatten_covers`), gate inputs sit strictly below their output (`flatten_scoped`), so
the values are pinned bottom-up. The forced extension of `flatten_sound` is THE satisfying
extension, not merely one of them. -/
theorem flatten_aux_unique (asg : Idx → F) (t : Term (AirSig F Idx)) (n₀ : ℕ)
    {auxv auxv' : ℕ → F} (h : gatesHold asg auxv (flatten t n₀).gates)
    (h' : gatesHold asg auxv' (flatten t n₀).gates) :
    ∀ m, n₀ ≤ m → m < (flatten t n₀).next → auxv m = auxv' m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm₀ hmn
    obtain ⟨g, hg, hgo⟩ := flatten_covers t n₀ m hm₀ hmn
    obtain ⟨-, -, hscoped⟩ := flatten_scoped t n₀
    obtain ⟨ha, hb, hlo, hhi⟩ := hscoped g hg
    have hagree : ∀ j, n₀ ≤ j → j < g.out → auxv j = auxv' j := fun j hj₁ hj₂ =>
      ih j (hgo ▸ hj₂) hj₁ (hj₂.trans_le (hgo ▸ hmn.le))
    have hra := WireRef.read_congr (asg := asg) hagree ha
    have hrb := WireRef.read_congr (asg := asg) hagree hb
    calc auxv m = auxv g.out := by rw [hgo]
      _ = g.op.denote (g.a.read asg auxv) (g.b.read asg auxv) := (h g hg).symm
      _ = g.op.denote (g.a.read asg auxv') (g.b.read asg auxv') := by rw [hra, hrb]
      _ = auxv' g.out := h' g hg
      _ = auxv' m := by rw [hgo]

/-- Root-level corollary: any two satisfying valuations read the ROOT identically — both are
forced to `eval asg t` (immediate from `flatten_forces`). -/
theorem flatten_root_forced (asg : Idx → F) (t : Term (AirSig F Idx)) (n₀ : ℕ)
    {auxv auxv' : ℕ → F} (h : gatesHold asg auxv (flatten t n₀).gates)
    (h' : gatesHold asg auxv' (flatten t n₀).gates) :
    (flatten t n₀).out.read asg auxv = (flatten t n₀).out.read asg auxv' := by
  rw [flatten_forces asg t n₀ auxv h, flatten_forces asg t n₀ auxv' h']

/-! ## §8. `flatten_constraint_iff` — the keystone: gate system ⟺ circuit ⟺ executor. -/

/-- **The keystone**: the flattened gate system, with the root output wire pinned to `0`, is
satisfiable (by SOME aux extension — equivalently by the forced one) iff the circuit accepts:
`eval asg t = 0`. Sound direction by wire-forcing (`flatten_forces`), complete direction by the
forced extension (`flatten_sound`). -/
theorem flatten_constraint_iff (asg : Idx → F) (t : Term (AirSig F Idx)) (n₀ : ℕ) :
    (∃ auxv : ℕ → F, gatesHold asg auxv (flatten t n₀).gates ∧
        (flatten t n₀).out.read asg auxv = 0)
      ↔ accepts asg t := by
  constructor
  · rintro ⟨auxv, hgates, hroot⟩
    show eval asg t = 0
    rw [← flatten_forces asg t n₀ auxv hgates]
    exact hroot
  · intro hacc
    obtain ⟨auxv, hgates, hroot⟩ := flatten_sound asg t n₀
    exact ⟨auxv, hgates, by rw [hroot]; exact hacc⟩

/-- **The full chain, closed**: the flattened gate system (+ root = 0) holds iff the EXECUTOR
relation holds — `flatten_constraint_iff` composed with rung 1's `accepts_iff_semHolds`. The
deployment-shaped gate system means exactly what the independent hand-recursed semantics say,
end to end, with no hand-authored constraint anywhere in the chain. -/
theorem flatten_constraint_iff_exec (asg : Idx → F) (t : Term (AirSig F Idx)) (n₀ : ℕ) :
    (∃ auxv : ℕ → F, gatesHold asg auxv (flatten t n₀).gates ∧
        (flatten t n₀).out.read asg auxv = 0)
      ↔ semHolds asg t := by
  rw [flatten_constraint_iff, accepts_iff_semHolds]

/-! ## §9. Keystone witnesses — BUILT, over `ZMod 7` (rung 1's example expression). -/

/-- The rung-1 example expression `(x + 2)·x` (Idx := Unit, F := ZMod 7). -/
def exFlat : Term (AirSig (ZMod 7) Unit) := mul' (add' (vr ()) (cst 2)) (vr ())

/-- The rung-1 assignment `x = 3`. -/
def exAsg : Unit → ZMod 7 := fun _ => 3

/-- The FORCED aux extension for `exFlat` at `x = 3`: wire 0 (the add node) ↦ `3+2 = 5`,
wire 1 (the mul node, the root) ↦ `5·3 = 15 = 1` over `ZMod 7`. -/
def exForced : ℕ → ZMod 7 := fun n => if n = 0 then 5 else 1

/-- *Computes*: `(x+2)·x` flattens to exactly TWO degree-≤2 gates — `x + 2 = aux₀` and
`aux₀ · x = aux₁` — with root wire `aux 1` and two allocations. -/
example : (flatten exFlat 0).gates
      = [⟨.add, .var (), .cnst 2, 0⟩, ⟨.mul, .aux 0, .var (), 1⟩]
    ∧ (flatten exFlat 0).out = .aux 1 ∧ (flatten exFlat 0).next = 2 :=
  ⟨rfl, rfl, rfl⟩

/-- *Satisfiable, BUILT*: the forced extension satisfies BOTH emitted gates, computed. -/
example : gatesHold exAsg exForced (flatten exFlat 0).gates := by
  intro g hg
  cases hg with
  | head => show (3 + 2 : ZMod 7) = 5; decide
  | tail _ hg' =>
    cases hg' with
    | head => show (5 * 3 : ZMod 7) = 1; decide
    | tail _ hg'' => exact nomatch hg''

/-- *...and the root wire reads the eval*: `aux 1` carries `eval exAsg exFlat = 1`. -/
example : (flatten exFlat 0).out.read exAsg exForced = eval exAsg exFlat := by decide

/-- *Teeth, BUILT*: a WRONG aux value (wire 0 ↦ 4 instead of the forced 5) VIOLATES the add
gate — the gates genuinely constrain the aux wires, not just the root. -/
example : ¬ Gate.holds exAsg (fun n => if n = 0 then (4 : ZMod 7) else 1)
    ⟨.add, .var (), .cnst 2, 0⟩ := by
  show ¬ ((3 + 2 : ZMod 7) = 4)
  decide

/-- *The keystone chain, accepting side*: at `x = 5`, `(5+2)·5 = 0` over `ZMod 7`, so the gate
system + root-wire-zero IS satisfiable — via `flatten_constraint_iff`, no witness constructed
by hand. -/
example : ∃ auxv : ℕ → ZMod 7,
    gatesHold (fun _ => (5 : ZMod 7)) auxv (flatten exFlat 0).gates ∧
      (flatten exFlat 0).out.read (fun _ => (5 : ZMod 7)) auxv = 0 := by
  rw [flatten_constraint_iff]
  show eval (fun _ => (5 : ZMod 7)) exFlat = 0
  decide

/-- *The keystone chain, rejecting side (teeth)*: at `x = 3` the expression evals to `1 ≠ 0`,
and by wire-forcing NO aux valuation whatsoever satisfies the gates with the root reading `0`. -/
example : ¬ ∃ auxv : ℕ → ZMod 7,
    gatesHold exAsg auxv (flatten exFlat 0).gates ∧
      (flatten exFlat 0).out.read exAsg auxv = 0 := by
  rw [flatten_constraint_iff]
  show ¬ (eval exAsg exFlat = 0)
  decide

end Minidregg.Compiler
