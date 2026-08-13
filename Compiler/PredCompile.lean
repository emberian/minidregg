/-
# `Compiler/PredCompile.lean` — [PRED-COMPILE]: the GENERAL `Pred → ConstraintSystem` compiler

ATLAS law 11 (widen the source, not the emitter) applied to `Compiler/`: until this file,
`Compiler/` was a GADGET LIBRARY — every constraint system (`boolGadget`, `rangeGadget`,
`noteSpend`, …) hand-instantiated, n = 1 each. This file is the n = ∀ transition: a lowering
from the `Pred` policy AST (`Pred/Core`, the ONE predicate algebra) to `ConstraintSystem`
(`Compiler/AirRange`), with ONE refinement theorem for ALL predicates.

**Substrate, said out loud: this is Lean-authored arithmetization, and the constraints come
out of a LOWERING FOLD over the `Pred` AST.** `lowerA`/`lowerL` is one structural recursion
over the policy algebra emitting DSL terms (`vr`/`cst`/`add'`/`mul'`, read through
`Compiler/Air`'s one fold); NO constraint is hand-written per predicate — a new policy
compiles without a new gadget — and the refinement `lower_correct` is ONE mutual induction
over `Pred`/`PredList`, not a per-gadget argument. Rust appears nowhere.

## Placement (the boundary question, resolved by reading, not vibes)

`scripts/check-import-boundary.sh` mechanically constrains ONLY `Theory/` and `Selvage/`;
`Compiler/` is not constrained by the script. `Pred/Core` imports core Lean only (it cannot
and does not import `Compiler`), so `Compiler → Pred.Core` introduces no cycle and keeps the
direction right: ATLAS §7 carves `Compiler/` as the arithmetization spine that CONSUMES
source vocabularies. The lowering therefore lives HERE, importing `Pred.Core`; the source
never learns the emitter.

## The compilation scheme (statement-first)

The step `(old, new)` is pinned onto INPUT wires (`Wire.val`, `Wire.pres` — value and
presence per slot, fail-closed absence made circuit-visible); the compiler allocates
AUXILIARY wires (`Wire.aux`, path-addressed by AST position) that the PROVER supplies —
exactly `AirFlatten`'s wire-forcing shape. Each node lowers to an INDICATOR term (a DSL
term whose value is forced to `if Pred.eval … then 1 else 0`) plus forcing constraints:

* `eq`/`memberOf` — the difference-is-zero (resp. product-of-differences) fed through the
  `isZero` combinator (two constraints `b·d ≐ 0`, `b + d·w − 1 ≐ 0` force `b = [d = 0]`),
  masked by the presence wire (fail-closed).
* `writeOnce` — presence-masked combination of two `isZero`s (`old = 0`, `new = old`).
* `witnessed` — the first-party evaluator FAILS CLOSED, so the indicator is the constant
  `0`; under `not` this composes correctly (`¬witnessed` is first-party TRUE).
* `not` — `1 − t`; `allL` — `∏ tᵢ`; `anyL` — `1 − ∏(1 − tᵢ)` (child aux wires disjoint by
  path prefixing, `pfx`).
* `le`/`monotone` — NOT lowered (order needs range decomposition): per ATLAS law 10 the
  refusal is LOUD — an unsatisfiable `1 ≐ 0`, never silence. `[PRED-COMPILE-order]` below.

The refinement (`lower_sound` + `lower_complete` = `lower_correct`) is a satisfiability
equivalence with the step wires PINNED and only the aux wires existential — the same shape
as `AirFlatten`'s gate-system refinement, and the only true shape (a pointwise iff over ALL
assignments is false for any aux-carrying system: junk aux must be rejectable):

  `(∃ A, systemAccepts (stepAsg old new A) (lower p)) ↔ Pred.eval p old new = true`

soundness quantifying over EVERY aux assignment (a forger cannot pick clever witnesses) and
completeness EXHIBITING the witness generator `wit` (derived in the same fold — the compiler
emits constraints AND the prover's witness routine from one recursion).

## Honest scope

* `castInjOn F (intsOf p old new)` — the deployment parameter constraint (the analog of
  `AirRange`'s `2^k ≤ p`): the finitely many `Int`s the instance touches must embed
  injectively into `F`. Not a residual — a label; `decide`-checkable per instance.
* `[PRED-COMPILE-order]` — `le`/`monotone` (Int order) need bounded-range decomposition
  (a bit-width parameter + `rangeGadget` reuse for `new − old` / `v − new`); today they
  lower to the LOUD unsatisfiable system (`lower_le_refuses`/`lower_monotone_refuses`) and
  are excluded from `supported`. The iff is stated (and proved) for the supported fragment.
* `[PRED-COMPILE-oracle]` — `witnessed` is compiled at its FIRST-PARTY semantics (`eval`,
  fail-closed — the iff genuinely holds). Arithmetizing an ORACLE-discharged claim
  (`evalWith O`) means importing the third party's verifier circuit (AirHash/AirMembership
  territory), not a per-predicate gadget.
* `[PRED-COMPILE-quant]` — `Pred/Core` has NO quantifier constructors today (the quantified
  views are `Pred/Placeholder` future work), so nothing is dropped here; when the source
  grows quantifiers, this compiler grows finite-domain expansion vocabulary — widen the
  source, then the lowering, never a bespoke gadget.
-/
import Pred.Core
import Compiler.AirRange

namespace Minidregg.Compiler

open Minidregg.Pred (Pred PredList State Slot Vk)

variable {F : Type} [Field F] {Idx Idx' : Type}

/-! ## §1. Wires — the step pinned on input wires, prover witnesses on path-addressed aux. -/

/-- The wire alphabet of a lowered policy: per-slot VALUE and PRESENCE input wires (the
(old, new) step, `isNew` selecting the side; presence makes `Pred`'s fail-closed absence
circuit-visible), plus PROVER-side auxiliary wires addressed by AST path (child index list)
and a node-local counter — path addressing keeps sibling aux disjoint by construction. -/
inductive Wire where
  /-- Value wire: `Int.cast` of the slot's value on the chosen side (`0` if absent). -/
  | val  (isNew : Bool) (s : Slot)
  /-- Presence wire: `1` if the slot is present on the chosen side, else `0`. -/
  | pres (isNew : Bool) (s : Slot)
  /-- Auxiliary (prover-supplied) wire at an AST path. -/
  | aux  (path : List ℕ) (k : ℕ)
deriving DecidableEq, Repr

/-- The value reading of a slot: `Int.cast` of the stored scalar, `0` if absent. -/
def valOf (st : State) (s : Slot) : F :=
  match st.get s with
  | some x => (x : F)
  | none   => 0

/-- The presence reading of a slot: `1` if present, `0` if absent. -/
def presOf (st : State) (s : Slot) : F :=
  cond (st.get s).isSome 1 0

/-- **The step assignment**: input wires pinned by the (old, new) step, aux wires supplied
by `A`. The refinement quantifies `A` (existential in `lower_correct`, universal in
`lower_sound`) while the step stays pinned. -/
def stepAsg (old new : State) (A : List ℕ → ℕ → F) : Wire → F
  | .val b s  => valOf (cond b new old) s
  | .pres b s => presOf (cond b new old) s
  | .aux p k  => A p k

/-- The `Int`s a state exposes (for the cast-injectivity label). -/
def stateVals (st : State) : List ℤ := st.slots.map (·.2)

theorem get_mem_stateVals {st : State} {s : Slot} {x : ℤ}
    (h : st.get s = some x) : x ∈ stateVals st := by
  unfold Minidregg.Pred.State.get at h
  cases hf : st.slots.find? (fun p => p.1 == s) with
  | none => rw [hf] at h; simp at h
  | some pr =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact List.mem_map.mpr ⟨pr, List.mem_of_find?_eq_some hf, h⟩

/-- **The deployment label** (analog of `AirRange`'s `2^k ≤ p`): the finitely many `Int`s
an instance touches embed injectively into `F`. Decidable on concrete instances. -/
def castInjOn (F : Type) [Field F] (I : List ℤ) : Prop :=
  ∀ a ∈ I, ∀ b ∈ I, (a : F) = (b : F) → a = b

theorem castInjOn_mono {I J : List ℤ} (hIJ : I ⊆ J) (h : castInjOn F J) :
    castInjOn F I :=
  fun a ha b hb => h a (hIJ ha) b (hIJ hb)

instance [DecidableEq F] (I : List ℤ) : Decidable (castInjOn F I) :=
  inferInstanceAs (Decidable (∀ a ∈ I, ∀ b ∈ I, (a : F) = (b : F) → a = b))

/-! ## §2. Wire renaming — a fold-level operation, so child aux namespaces compose. -/

/-- Rename the variables of a DSL term (the only payload-carrying leaf). -/
def renameT (f : Idx → Idx') : Term (AirSig F Idx) → Term (AirSig F Idx')
  | .mk (.const c) _ => cst c
  | .mk (.var i) _   => vr (f i)
  | .mk .add k       => add' (renameT f (k false)) (renameT f (k true))
  | .mk .mul k       => mul' (renameT f (k false)) (renameT f (k true))

/-- Raw-node computation rules for `eval` (the `add'`/`mul'` rules of `AirRange` §2 cover
smart-constructor nodes; these cover an arbitrary child family). -/
@[simp] theorem eval_mkAdd (asg : Idx → F) (k : Bool → Term (AirSig F Idx)) :
    eval asg (.mk .add k) = eval asg (k false) + eval asg (k true) := rfl

@[simp] theorem eval_mkMul (asg : Idx → F) (k : Bool → Term (AirSig F Idx)) :
    eval asg (.mk .mul k) = eval asg (k false) * eval asg (k true) := rfl

/-- Renaming is evaluation under the composed assignment. -/
theorem eval_renameT (asg : Idx' → F) (f : Idx → Idx') :
    ∀ t : Term (AirSig F Idx), eval asg (renameT f t) = eval (asg ∘ f) t
  | .mk (.const _) _ => rfl
  | .mk (.var _) _   => rfl
  | .mk .add k       => by
      simp only [renameT, eval_add', eval_mkAdd,
        eval_renameT asg f (k false), eval_renameT asg f (k true)]
  | .mk .mul k       => by
      simp only [renameT, eval_mul', eval_mkMul,
        eval_renameT asg f (k false), eval_renameT asg f (k true)]

theorem accepts_renameT (asg : Idx' → F) (f : Idx → Idx') (t : Term (AirSig F Idx)) :
    accepts asg (renameT f t) ↔ accepts (asg ∘ f) t := by
  unfold accepts; rw [eval_renameT]

/-- Rename a whole system. -/
def renameS (f : Idx → Idx') (sys : ConstraintSystem F Idx) : ConstraintSystem F Idx' :=
  sys.map (renameT f)

theorem systemAccepts_renameS (asg : Idx' → F) (f : Idx → Idx')
    (sys : ConstraintSystem F Idx) :
    systemAccepts asg (renameS f sys) ↔ systemAccepts (asg ∘ f) sys := by
  unfold systemAccepts renameS
  constructor
  · intro h t ht
    rw [← accepts_renameT asg f t]
    exact h _ (List.mem_map.mpr ⟨t, ht, rfl⟩)
  · intro h t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    rw [accepts_renameT]
    exact h u hu

/-- Prefix a child index onto every aux path (input wires fixed). -/
def pfx (i : ℕ) : Wire → Wire
  | .aux p k => .aux (i :: p) k
  | w        => w

theorem stepAsg_pfx (old new : State) (A : List ℕ → ℕ → F) (i : ℕ) :
    stepAsg old new A ∘ pfx i = stepAsg old new (fun p k => A (i :: p) k) := by
  funext w; cases w <;> rfl

/-! ## §3. Structural `systemAccepts` lemmas — REUSED from `AirRange` §1
(`systemAccepts_nil`/`systemAccepts_cons`/`systemAccepts_append`), not re-derived. -/

/-! ## §4. Compiler combinators — `notT`/`prodT` (indicator algebra) and `isZero` (the one
witness-carrying primitive; everything else is polynomial in forced indicators). -/

/-- Indicator negation: `1 − t`. -/
def notT (t : Term (AirSig F Idx)) : Term (AirSig F Idx) :=
  add' (cst 1) (mul' (cst (-1)) t)

@[simp] theorem eval_notT (asg : Idx → F) (t : Term (AirSig F Idx)) :
    eval asg (notT t) = 1 - eval asg t := by
  simp only [notT, eval_add', eval_mul', eval_cst]
  ring

/-- Indicator product: `∏ tᵢ` (empty = `1`). -/
def prodT (l : List (Term (AirSig F Idx))) : Term (AirSig F Idx) :=
  l.foldr mul' (cst 1)

@[simp] theorem eval_prodT (asg : Idx → F) (l : List (Term (AirSig F Idx))) :
    eval asg (prodT l) = (l.map (eval asg)).prod := by
  induction l with
  | nil => simp [prodT]
  | cons t l ih =>
    show eval asg (mul' t (prodT l)) = _
    rw [eval_mul', ih, List.map_cons, List.prod_cons]

section DecEqF
variable [DecidableEq F]

/-- **The is-zero combinator** — the single witness-carrying primitive of the compiler:
wires `b` (the forced indicator) and `w` (the inverse witness) with constraints
`b·d ≐ 0` and `b + d·w − 1 ≐ 0`. Every atom's decision routes through this; no
per-predicate constraint is ever hand-written. -/
def isZero (d : Term (AirSig F Idx)) (b w : Idx) : ConstraintSystem F Idx :=
  [mul' (vr b) d, add' (add' (vr b) (mul' d (vr w))) (cst (-1))]

/-- The is-zero wires are FORCED: any accepted assignment has `b = [d = 0]`. -/
theorem isZero_forced {asg : Idx → F} {d : Term (AirSig F Idx)} {b w : Idx}
    (h : systemAccepts asg (isZero d b w)) :
    asg b = if eval asg d = 0 then 1 else 0 := by
  rw [isZero, systemAccepts_cons, systemAccepts_cons] at h
  obtain ⟨h₁, h₂, -⟩ := h
  unfold accepts at h₁ h₂
  simp only [eval_mul', eval_add', eval_vr, eval_cst] at h₁ h₂
  by_cases hd : eval asg d = 0
  · rw [if_pos hd]
    rw [hd, zero_mul] at h₂
    linear_combination h₂
  · rw [if_neg hd]
    rcases mul_eq_zero.mp h₁ with hb | hd'
    · exact hb
    · exact absurd hd' hd

/-- The is-zero constraints are SATISFIABLE at the canonical witness values. -/
theorem isZero_complete {asg : Idx → F} {d : Term (AirSig F Idx)} {b w : Idx}
    (hb : asg b = if eval asg d = 0 then 1 else 0)
    (hw : asg w = if eval asg d = 0 then 0 else (eval asg d)⁻¹) :
    systemAccepts asg (isZero d b w) := by
  rw [isZero, systemAccepts_cons, systemAccepts_cons]
  refine ⟨?_, ?_, systemAccepts_nil _⟩ <;> unfold accepts <;>
    simp only [eval_mul', eval_add', eval_vr, eval_cst] <;>
    by_cases hd : eval asg d = 0
  · rw [hd, mul_zero]
  · rw [hb, if_neg hd, zero_mul]
  · rw [hb, hw, if_pos hd, if_pos hd, hd, zero_mul]; ring
  · rw [hb, hw, if_neg hd, if_neg hd, mul_inv_cancel₀ hd]; ring

/-- The canonical is-zero witness pair for a difference value `dv`: aux `0` carries the
indicator, aux `1` the inverse witness. -/
def auxPair (dv : F) : ℕ → F := fun k =>
  if k = 0 then (if dv = 0 then 1 else 0)
  else if k = 1 then (if dv = 0 then 0 else dv⁻¹)
  else 0

end DecEqF

/-! ## §5. The difference terms of the atoms — DSL terms over input wires only. -/

/-- `eq` difference: `val(new, s) − v`. -/
def eqD (s : Slot) (v : ℤ) : Term (AirSig F Wire) :=
  add' (vr (.val true s)) (cst (-(v : F)))

/-- `memberOf` difference: `∏_{c ∈ xs} (val(new, s) − c)`. -/
def memD (s : Slot) (xs : List ℤ) : Term (AirSig F Wire) :=
  prodT (xs.map fun c : ℤ => add' (vr (.val true s)) (cst (-(c : F))))

/-- `writeOnce` first difference: `val(old, s)` (is the old value `0`?). -/
def woD1 (s : Slot) : Term (AirSig F Wire) := vr (.val false s)

/-- `writeOnce` second difference: `val(new, s) − val(old, s)`. -/
def woD2 (s : Slot) : Term (AirSig F Wire) :=
  add' (vr (.val true s)) (mul' (cst (-1)) (vr (.val false s)))

@[simp] theorem eval_eqD (old new : State) (A : List ℕ → ℕ → F) (s : Slot) (v : ℤ) :
    eval (stepAsg old new A) (eqD s v) = valOf new s - (v : F) := by
  simp only [eqD, eval_add', eval_vr, eval_cst, stepAsg, cond_true]
  ring

@[simp] theorem eval_memD (old new : State) (A : List ℕ → ℕ → F) (s : Slot)
    (xs : List ℤ) :
    eval (stepAsg old new A) (memD s xs)
      = (xs.map fun c : ℤ => valOf new s - (c : F)).prod := by
  simp only [memD, eval_prodT, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_apply, eval_add', eval_vr, eval_cst, stepAsg, cond_true]
  ring

@[simp] theorem eval_woD1 (old new : State) (A : List ℕ → ℕ → F) (s : Slot) :
    eval (stepAsg old new A) (woD1 s) = valOf old s := rfl

@[simp] theorem eval_woD2 (old new : State) (A : List ℕ → ℕ → F) (s : Slot) :
    eval (stepAsg old new A) (woD2 s) = valOf new s - valOf old s := by
  simp only [woD2, eval_add', eval_mul', eval_vr, eval_cst, stepAsg, cond_true, cond_false]
  ring

/-! ## §6. THE LOWERING — one structural fold over the `Pred` AST. Each node yields an
indicator TERM (forced to `[Pred.eval]`) and forcing CONSTRAINTS; nothing else, for any
predicate, ever. -/

mutual
/-- **The lowering fold** (per node): indicator term + forcing constraints. Aux wires of
this node live at path `[]`; children of `allL`/`anyL` are renamed under their child index
(`pfx`), keeping sibling witnesses disjoint by construction. -/
def lowerA : Pred → Term (AirSig F Wire) × ConstraintSystem F Wire
  | .eq s v =>
      (mul' (vr (.pres true s)) (vr (.aux [] 0)),
       isZero (eqD s v) (.aux [] 0) (.aux [] 1))
  | .le _ _ =>
      (cst 0, [cst 1])   -- [PRED-COMPILE-order]: LOUD unsatisfiable (ATLAS law 10)
  | .memberOf s xs =>
      (mul' (vr (.pres true s)) (vr (.aux [] 0)),
       isZero (memD s xs) (.aux [] 0) (.aux [] 1))
  | .writeOnce s =>
      (notT (mul' (vr (.pres false s))
        (mul' (notT (vr (.aux [] 0)))
              (notT (mul' (vr (.pres true s)) (vr (.aux [] 2)))))),
       isZero (woD1 s) (.aux [] 0) (.aux [] 1)
         ++ isZero (woD2 s) (.aux [] 2) (.aux [] 3))
  | .monotone _ =>
      (cst 0, [cst 1])   -- [PRED-COMPILE-order]: LOUD unsatisfiable (ATLAS law 10)
  | .witnessed _ =>
      (cst 0, [])        -- first-party fail-closed: the indicator is constant 0
  | .not p =>
      let l := lowerA p
      (notT l.1, l.2)
  | .allL ps =>
      let l := lowerL ps 0
      (prodT l.1, l.2)
  | .anyL ps =>
      let l := lowerL ps 0
      (notT (prodT (l.1.map notT)), l.2)

/-- Child lowering: each child renamed under its position index. -/
def lowerL : PredList → ℕ → List (Term (AirSig F Wire)) × ConstraintSystem F Wire
  | .nil, _ => ([], [])
  | .cons p ps, i =>
      let hd := lowerA p
      let tl := lowerL ps (i + 1)
      (renameT (pfx i) hd.1 :: tl.1, renameS (pfx i) hd.2 ++ tl.2)
end

/-- **`lower`** — the compiled system: the forcing constraints plus the top-level
assertion `indicator ≐ 1`. -/
def lower (p : Pred) : ConstraintSystem F Wire :=
  (lowerA p).2 ++ [add' (lowerA p).1 (cst (-1))]

/-! ## §7. The supported fragment and the cast-injectivity label. -/

mutual
/-- The fragment this compiler lowers faithfully: everything except the order atoms
(`le`/`monotone` — `[PRED-COMPILE-order]`). Decidable, structural. -/
def supported : Pred → Bool
  | .eq _ _       => true
  | .le _ _       => false
  | .memberOf _ _ => true
  | .writeOnce _  => true
  | .monotone _   => false
  | .witnessed _  => true
  | .not p        => supported p
  | .allL ps      => supportedL ps
  | .anyL ps      => supportedL ps

def supportedL : PredList → Bool
  | .nil       => true
  | .cons p ps => supported p && supportedL ps
end

mutual
/-- The `Int` literals a predicate mentions (for the injectivity label). -/
def lits : Pred → List ℤ
  | .eq _ v       => [v]
  | .le _ v       => [v]
  | .memberOf _ xs => xs
  | .writeOnce _  => []
  | .monotone _   => []
  | .witnessed _  => []
  | .not p        => lits p
  | .allL ps      => litsL ps
  | .anyL ps      => litsL ps

def litsL : PredList → List ℤ
  | .nil       => []
  | .cons p ps => lits p ++ litsL ps
end

/-- All `Int`s an instance touches: `0` (the `writeOnce` sentinel), the predicate's
literals, and both states' values. -/
def intsOf (p : Pred) (old new : State) : List ℤ :=
  0 :: (lits p ++ stateVals old ++ stateVals new)

/-! ## §8. The witness generator — derived in the same fold (the prover routine the
compiler emits alongside the constraints). -/

section DecEqF
variable [DecidableEq F]

mutual
/-- The canonical aux assignment making a TRUE (supported) predicate's system accept. -/
def wit : Pred → State → State → List ℕ → ℕ → F
  | .eq s v       => fun _ new _ k => auxPair (valOf new s - (v : F)) k
  | .le _ _       => fun _ _ _ _ => 0
  | .memberOf s xs => fun _ new _ k =>
      auxPair ((xs.map fun c : ℤ => valOf new s - (c : F)).prod) k
  | .writeOnce s  => fun old new _ k =>
      if k < 2 then auxPair (valOf old s) k
      else auxPair (valOf new s - valOf old s) (k - 2)
  | .monotone _   => fun _ _ _ _ => 0
  | .witnessed _  => fun _ _ _ _ => 0
  | .not p        => wit p
  | .allL ps      => witL ps 0
  | .anyL ps      => witL ps 0

def witL : PredList → ℕ → State → State → List ℕ → ℕ → F
  | .nil, _       => fun _ _ _ _ => 0
  | .cons p ps, i => fun old new path k =>
      match path with
      | []        => 0
      | j :: rest => if j = i then wit p old new rest k
                     else witL ps (i + 1) old new (j :: rest) k
end

end DecEqF

/-! ## §9. Indicator arithmetic over `F` — tiny list lemmas the induction leans on. -/

theorem prod_ind {α : Type} (l : List α) (f : α → Bool) :
    (l.map fun q => if f q = true then (1 : F) else 0).prod
      = if l.all f = true then 1 else 0 := by
  induction l with
  | nil => simp
  | cons q l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.all_cons]
    cases hf : f q <;> cases hl : l.all f <;> simp

theorem prod_one_sub_ind {α : Type} (l : List α) (f : α → Bool) :
    ((l.map fun q => if f q = true then (1 : F) else 0).map (fun x => 1 - x)).prod
      = if (l.all fun q => !f q) = true then 1 else 0 := by
  rw [List.map_map]
  have h : ((fun x => (1 : F) - x) ∘ fun q => if f q = true then (1 : F) else 0)
      = fun q => if (!f q) = true then (1 : F) else 0 := by
    funext q; cases hf : f q <;> simp [hf]
  rw [h, prod_ind]

theorem all_not_eq_not_any {α : Type} (l : List α) (f : α → Bool) :
    (l.all fun a => !f a) = !l.any f := by
  induction l with
  | nil => rfl
  | cons a l ih => cases hf : f a <;> simp [List.all_cons, List.any_cons, hf, ih]

theorem one_sub_ind (b : Bool) :
    (1 : F) - (if b = true then 1 else 0) = if (!b) = true then 1 else 0 := by
  cases b <;> simp

theorem one_sub_ind_not (b : Bool) :
    (1 : F) - (if (!b) = true then 1 else 0) = if b = true then 1 else 0 := by
  cases b <;> simp

theorem eval_prodT_notT (asg : Idx → F) (l : List (Term (AirSig F Idx))) :
    eval asg (prodT (l.map notT)) = ((l.map (eval asg)).map (fun x => 1 - x)).prod := by
  rw [eval_prodT, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun _ _ => by simp [Function.comp_apply, eval_notT]

/-- `Pred.evalWithAll` over the inlined list is `List.all` over `toList`. -/
theorem evalWithAll_toList (O : Minidregg.Pred.Oracle) (ps : PredList)
    (old new : State) :
    Minidregg.Pred.evalWithAll O ps old new
      = ps.toList.all fun q => Minidregg.Pred.evalWith O q old new := by
  conv_lhs => rw [← Minidregg.Pred.PredList.ofList_toList ps]
  exact Minidregg.Pred.evalWithAll_ofList O ps.toList old new

/-- `Pred.evalWithAny` over the inlined list is `List.any` over `toList`. -/
theorem evalWithAny_toList (O : Minidregg.Pred.Oracle) (ps : PredList)
    (old new : State) :
    Minidregg.Pred.evalWithAny O ps old new
      = ps.toList.any fun q => Minidregg.Pred.evalWith O q old new := by
  conv_lhs => rw [← Minidregg.Pred.PredList.ofList_toList ps]
  exact Minidregg.Pred.evalWithAny_ofList O ps.toList old new

/-! ## §10. FORCING — the general soundness induction: on EVERY accepted assignment the
indicator term evaluates to exactly `[Pred.eval]`. One mutual induction, all constructors,
no per-gadget argument. -/

section DecEqF
variable [DecidableEq F]

-- (the mutual block generalizes section variables jointly; the linter's per-theorem
-- "unused [DecidableEq F]" on `lowerL_forced` is a mutual-block artifact)
set_option linter.unusedSectionVars false in
mutual
theorem lowerA_forced :
    ∀ (p : Pred) (old new : State) (A : List ℕ → ℕ → F),
      castInjOn F (intsOf p old new) → supported p = true →
      systemAccepts (stepAsg old new A) (lowerA p).2 →
      eval (stepAsg old new A) (lowerA p).1
        = if Minidregg.Pred.eval p old new = true then 1 else 0
  | .eq s v, old, new, A, hinj, _, h => by
    simp only [lowerA] at h ⊢
    have hb := isZero_forced h
    simp only [eval_mul', eval_vr, hb, eval_eqD]
    show presOf new s * _ = _
    cases hget : new.get s with
    | none =>
      simp [presOf, hget, Minidregg.Pred.eval, Minidregg.Pred.evalWith]
    | some x =>
      have hx : x ∈ intsOf (.eq s v) old new := by
        simp [intsOf, List.mem_append, get_mem_stateVals hget]
      have hv : v ∈ intsOf (.eq s v) old new := by simp [intsOf, lits]
      simp only [presOf, hget, Option.isSome_some, cond_true, one_mul, valOf,
        Minidregg.Pred.eval, Minidregg.Pred.evalWith, Option.some.injEq]
      by_cases hxv : x = v
      · simp [hxv]
      · have : ¬((x : F) - (v : F) = 0) := fun hc =>
          hxv (hinj x hx v hv (sub_eq_zero.mp hc))
        simp [hxv, this]
  | .le s v, old, new, A, _, hsup, h => by
    simp [supported] at hsup
  | .memberOf s xs, old, new, A, hinj, _, h => by
    simp only [lowerA] at h ⊢
    have hb := isZero_forced h
    simp only [eval_mul', eval_vr, hb, eval_memD]
    show presOf new s * _ = _
    cases hget : new.get s with
    | none =>
      simp [presOf, hget, Minidregg.Pred.eval, Minidregg.Pred.evalWith]
    | some x =>
      have hx : x ∈ intsOf (.memberOf s xs) old new := by
        simp [intsOf, List.mem_append, get_mem_stateVals hget]
      simp only [presOf, hget, Option.isSome_some, cond_true, one_mul, valOf,
        Minidregg.Pred.eval, Minidregg.Pred.evalWith]
      by_cases hmem : x ∈ xs
      · simp only [List.contains_iff_mem, hmem, if_true]
        simp only [List.prod_eq_zero_iff, List.mem_map]
        rw [if_pos ⟨x, hmem, sub_self _⟩]
      · simp only [List.contains_iff_mem, hmem, if_false]
        simp only [List.prod_eq_zero_iff, List.mem_map]
        rw [if_neg]
        rintro ⟨c, hc, hc0⟩
        have hcI : c ∈ intsOf (.memberOf s xs) old new := by
          simp [intsOf, lits, List.mem_append, hc]
        have hxc : x = c := hinj x hx c hcI (sub_eq_zero.mp hc0)
        rw [hxc] at hmem
        exact hmem hc
  | .writeOnce s, old, new, A, hinj, _, h => by
    simp only [lowerA, systemAccepts_append] at h
    obtain ⟨h₁, h₂⟩ := h
    have hb₁ := isZero_forced h₁
    have hb₂ := isZero_forced h₂
    simp only [lowerA, eval_notT, eval_mul', eval_vr, hb₁, hb₂, eval_woD1, eval_woD2]
    simp only [stepAsg, cond_true, cond_false]
    cases hgo : old.get s with
    | none =>
      simp [presOf, hgo, Minidregg.Pred.eval, Minidregg.Pred.evalWith]
    | some o =>
      have ho : o ∈ intsOf (.writeOnce s) old new := by
        simp [intsOf, List.mem_append, get_mem_stateVals hgo]
      have h0 : (0 : ℤ) ∈ intsOf (.writeOnce s) old new := by simp [intsOf]
      simp only [presOf, valOf, hgo, Option.isSome_some, cond_true, one_mul,
        Minidregg.Pred.eval, Minidregg.Pred.evalWith]
      by_cases ho0 : o = 0
      · simp [ho0]
      · have hoF : ¬((o : F) = 0) := fun hc =>
          ho0 (hinj o ho 0 h0 (by rw [hc]; exact (Int.cast_zero).symm))
        have hbeq : (o == 0) = false := by
          simp [ho0]
        rw [if_neg hoF]
        cases hgn : new.get s with
        | none =>
          simp [hbeq]
        | some n =>
          have hn : n ∈ intsOf (.writeOnce s) old new := by
            simp [intsOf, List.mem_append, get_mem_stateVals hgn]
          simp only [Option.isSome_some, cond_true, one_mul,
            hbeq, Bool.false_or, Option.some.injEq]
          by_cases hno : n = o
          · simp [hno]
          · have hsub : ¬((n : F) - (o : F) = 0) := fun hc =>
              hno (hinj n hn o ho (sub_eq_zero.mp hc))
            simp [hno, hsub]
  | .monotone s, old, new, A, _, hsup, h => by
    simp [supported] at hsup
  | .witnessed vk, old, new, A, _, _, _ => by
    simp [lowerA, eval_cst, Minidregg.Pred.eval, Minidregg.Pred.evalWith,
      Minidregg.Pred.failClosed]
  | .not p, old, new, A, hinj, hsup, h => by
    simp only [supported] at hsup
    have hinj' : castInjOn F (intsOf p old new) := by
      simpa only [intsOf, lits] using hinj
    simp only [lowerA] at h ⊢
    rw [eval_notT, lowerA_forced p old new A hinj' hsup h]
    simp only [Minidregg.Pred.eval, Minidregg.Pred.evalWith]
    exact one_sub_ind _
  | .allL ps, old, new, A, hinj, hsup, h => by
    simp only [supported] at hsup
    have hinj' : castInjOn F (0 :: (litsL ps ++ stateVals old ++ stateVals new)) := by
      simpa only [intsOf, lits] using hinj
    simp only [lowerA] at h ⊢
    rw [eval_prodT, lowerL_forced ps 0 old new A hinj' hsup h, prod_ind]
    simp only [Minidregg.Pred.eval, Minidregg.Pred.evalWith, evalWithAll_toList]
    rfl
  | .anyL ps, old, new, A, hinj, hsup, h => by
    simp only [supported] at hsup
    have hinj' : castInjOn F (0 :: (litsL ps ++ stateVals old ++ stateVals new)) := by
      simpa only [intsOf, lits] using hinj
    simp only [lowerA] at h ⊢
    rw [eval_notT, eval_prodT_notT, lowerL_forced ps 0 old new A hinj' hsup h,
      prod_one_sub_ind, all_not_eq_not_any]
    simp only [Minidregg.Pred.eval, Minidregg.Pred.evalWith, evalWithAny_toList]
    exact one_sub_ind_not _

theorem lowerL_forced :
    ∀ (ps : PredList) (i : ℕ) (old new : State) (A : List ℕ → ℕ → F),
      castInjOn F (0 :: (litsL ps ++ stateVals old ++ stateVals new)) →
      supportedL ps = true →
      systemAccepts (stepAsg old new A) (lowerL ps i).2 →
      (lowerL ps i).1.map (eval (stepAsg old new A))
        = ps.toList.map fun q =>
            if Minidregg.Pred.eval q old new = true then 1 else 0
  | .nil, _, _, _, _, _, _, _ => rfl
  | .cons p ps, i, old, new, A, hinj, hsup, h => by
    simp only [supportedL, Bool.and_eq_true] at hsup
    simp only [lowerL, systemAccepts_append] at h
    obtain ⟨h₁, h₂⟩ := h
    rw [systemAccepts_renameS, stepAsg_pfx] at h₁
    have hinjp : castInjOn F (intsOf p old new) :=
      castInjOn_mono (by
        intro a ha
        simp only [intsOf, litsL, List.mem_cons, List.mem_append] at ha ⊢
        tauto) hinj
    have hinjps : castInjOn F (0 :: (litsL ps ++ stateVals old ++ stateVals new)) :=
      castInjOn_mono (by
        intro a ha
        simp only [litsL, List.mem_cons, List.mem_append] at ha ⊢
        tauto) hinj
    have ih₁ := lowerA_forced p old new (fun path k => A (i :: path) k)
      hinjp hsup.1 h₁
    have ih₂ := lowerL_forced ps (i + 1) old new A hinjps hsup.2 h₂
    simp only [lowerL, Minidregg.Pred.PredList.toList, List.map_cons]
    rw [eval_renameT, stepAsg_pfx, ih₁, ih₂]
end

end DecEqF

/-! ## §11. COMPLETENESS — the emitted witness generator accepts every TRUE (supported)
instance. Same mutual induction; the child-agreement hypothesis (`hA`) is how sibling
witness namespaces paste without any scoping side-conditions. -/

section DecEqF
variable [DecidableEq F]

mutual
theorem lowerA_complete :
    ∀ (p : Pred) (old new : State), supported p = true →
      systemAccepts (stepAsg old new (wit (F := F) p old new)) (lowerA p).2
  | .eq s v, old, new, _ => by
    simp only [lowerA]
    apply isZero_complete
    · show auxPair (valOf new s - (v : F)) 0 = _
      rw [eval_eqD]; simp [auxPair]
    · show auxPair (valOf new s - (v : F)) 1 = _
      rw [eval_eqD]; simp [auxPair]
  | .le s v, old, new, hsup => by simp [supported] at hsup
  | .memberOf s xs, old, new, _ => by
    simp only [lowerA]
    apply isZero_complete
    · show auxPair ((xs.map fun c : ℤ => valOf new s - (c : F)).prod) 0 = _
      rw [eval_memD]; simp [auxPair]
    · show auxPair ((xs.map fun c : ℤ => valOf new s - (c : F)).prod) 1 = _
      rw [eval_memD]; simp [auxPair]
  | .writeOnce s, old, new, _ => by
    simp only [lowerA, systemAccepts_append]
    constructor
    · apply isZero_complete
      · show (if (0 : ℕ) < 2 then auxPair (valOf old s) 0
              else auxPair (valOf new s - valOf old s) (0 - 2)) = _
        rw [eval_woD1]; simp [auxPair]
      · show (if (1 : ℕ) < 2 then auxPair (valOf old s) 1
              else auxPair (valOf new s - valOf old s) (1 - 2)) = _
        rw [eval_woD1]; simp [auxPair]
    · apply isZero_complete
      · show (if (2 : ℕ) < 2 then auxPair (valOf old s) 2
              else auxPair (valOf new s - valOf old s) (2 - 2)) = _
        rw [eval_woD2]; simp [auxPair]
      · show (if (3 : ℕ) < 2 then auxPair (valOf old s) 3
              else auxPair (valOf new s - valOf old s) (3 - 2)) = _
        rw [eval_woD2]; simp [auxPair]
  | .monotone s, old, new, hsup => by simp [supported] at hsup
  | .witnessed vk, old, new, _ => by
    simp only [lowerA]
    exact systemAccepts_nil _
  | .not p, old, new, hsup => by
    simp only [supported] at hsup
    simp only [lowerA, wit]
    exact lowerA_complete p old new hsup
  | .allL ps, old, new, hsup => by
    simp only [supported] at hsup
    simp only [lowerA, wit]
    exact lowerL_complete ps 0 old new (witL ps 0 old new)
      (fun _ _ _ _ => rfl) hsup
  | .anyL ps, old, new, hsup => by
    simp only [supported] at hsup
    simp only [lowerA, wit]
    exact lowerL_complete ps 0 old new (witL ps 0 old new)
      (fun _ _ _ _ => rfl) hsup

theorem lowerL_complete :
    ∀ (ps : PredList) (i : ℕ) (old new : State) (A : List ℕ → ℕ → F),
      (∀ j, i ≤ j → ∀ path k, A (j :: path) k = witL ps i old new (j :: path) k) →
      supportedL ps = true →
      systemAccepts (stepAsg old new A) (lowerL ps i).2
  | .nil, _, _, _, _, _, _ => systemAccepts_nil _
  | .cons p ps, i, old, new, A, hA, hsup => by
    simp only [supportedL, Bool.and_eq_true] at hsup
    simp only [lowerL, systemAccepts_append]
    constructor
    · rw [systemAccepts_renameS, stepAsg_pfx]
      have hfun : (fun path k => A (i :: path) k) = wit p old new := by
        funext path k
        rw [hA i (le_refl i) path k]
        simp [witL]
      rw [hfun]
      exact lowerA_complete p old new hsup.1
    · refine lowerL_complete ps (i + 1) old new A ?_ hsup.2
      intro j hj path k
      rw [hA j (by omega) path k]
      simp only [witL]
      rw [if_neg (by omega)]
end

end DecEqF

/-! ## §12. THE KEYSTONE — `lower_sound` / `lower_complete` / `lower_correct`: the general
compiler refinement, one theorem for ALL predicates in the supported fragment. -/

section DecEqF
variable [DecidableEq F]

/-- **General soundness** (∀ aux — a forger cannot pick clever witnesses): any accepted
assignment with the step pinned means the policy HOLDS. -/
theorem lower_sound {p : Pred} {old new : State} {A : List ℕ → ℕ → F}
    (hinj : castInjOn F (intsOf p old new)) (hsup : supported p = true)
    (h : systemAccepts (stepAsg old new A) (lower p)) :
    Minidregg.Pred.eval p old new = true := by
  rw [lower, systemAccepts_append, systemAccepts_cons] at h
  obtain ⟨hsys, htop, -⟩ := h
  unfold accepts at htop
  rw [eval_add', eval_cst, lowerA_forced p old new A hinj hsup hsys] at htop
  by_cases he : Minidregg.Pred.eval p old new = true
  · exact he
  · rw [if_neg he] at htop
    exact absurd (by linear_combination htop : (0 : F) = 1) zero_ne_one

/-- **General completeness**: a TRUE (supported) policy's system accepts at the emitted
witness generator `wit`. -/
theorem lower_complete {p : Pred} {old new : State}
    (hinj : castInjOn F (intsOf p old new)) (hsup : supported p = true)
    (he : Minidregg.Pred.eval p old new = true) :
    systemAccepts (stepAsg old new (wit (F := F) p old new)) (lower p) := by
  rw [lower, systemAccepts_append, systemAccepts_cons]
  have hsys := lowerA_complete (F := F) p old new hsup
  refine ⟨hsys, ?_, systemAccepts_nil _⟩
  unfold accepts
  rw [eval_add', eval_cst,
    lowerA_forced p old new (wit p old new) hinj hsup hsys, if_pos he]
  ring

/-- **`lower_correct` — THE general compiler refinement** (the n = ∀ theorem): with the
step pinned on the input wires and the aux wires prover-existential, the compiled system
accepts **iff** the predicate holds — for EVERY predicate of the supported fragment, by one
mutual induction over the `Pred` AST. No bespoke gadget, no per-predicate argument. -/
theorem lower_correct {p : Pred} {old new : State}
    (hinj : castInjOn F (intsOf p old new)) (hsup : supported p = true) :
    (∃ A : List ℕ → ℕ → F, systemAccepts (stepAsg old new A) (lower p))
      ↔ Minidregg.Pred.eval p old new = true :=
  ⟨fun ⟨_, h⟩ => lower_sound hinj hsup h,
   fun he => ⟨wit p old new, lower_complete hinj hsup he⟩⟩

end DecEqF

/-! ## §13. LOUD refusal (ATLAS law 10) — the order atoms are not silently dropped: their
lowering rejects EVERYTHING, on any assignment, any field. -/

theorem lower_le_refuses (s : Slot) (v : ℤ) (asg : Wire → F) :
    ¬ systemAccepts asg (lower (.le s v)) := fun h =>
  one_ne_zero (h (cst 1) (List.mem_append_left _ (List.mem_cons_self)))

theorem lower_monotone_refuses (s : Slot) (asg : Wire → F) :
    ¬ systemAccepts asg (lower (.monotone s)) := fun h =>
  one_ne_zero (h (cst 1) (List.mem_append_left _ (List.mem_cons_self)))

/-! ## §14. SUBSUMPTION — the general compiler reproduces the hand gadget (n = 1 → n = ∀).

Booleanity as a POLICY (`x = 0 ∨ x = 1`, said in `Pred`) compiles — through the general
`lower_correct`, no bespoke construction — to a system whose verdict coincides with rung
1's hand-written `boolGadget` on the same value. The gadget library is now a special case
of the compiler. -/

/-- Booleanity said in the source language: `new[s] = 0 ∨ new[s] = 1`. -/
def boolPol (s : Slot) : Pred := Pred.any [.eq s 0, .eq s 1]

section DecEqF
variable [DecidableEq F]

/-- **The subsumption theorem**: on a present slot (with the cast label), the GENERAL
compiler's verdict on the booleanity POLICY is exactly the hand-written `boolGadget`'s
verdict on the value wire. -/
theorem lower_subsumes_boolGadget {old new : State} {s : Slot} {x : ℤ}
    (hget : new.get s = some x)
    (hinj : castInjOn F (intsOf (boolPol s) old new)) :
    (∃ A : List ℕ → ℕ → F, systemAccepts (stepAsg old new A) (lower (boolPol s)))
      ↔ accepts (fun _ : Unit => (x : F)) (boolGadget ()) := by
  rw [lower_correct hinj rfl, boolGadget_correct]
  have h0 : (0 : ℤ) ∈ intsOf (boolPol s) old new := by simp [intsOf]
  have h1 : (1 : ℤ) ∈ intsOf (boolPol s) old new := by
    simp [intsOf, boolPol, Pred.any, Minidregg.Pred.PredList.ofList, lits, litsL]
  have hx : x ∈ intsOf (boolPol s) old new := by
    simp [intsOf, List.mem_append, get_mem_stateVals hget]
  simp only [boolPol, Minidregg.Pred.eval, Minidregg.Pred.evalWith_any, List.any_cons,
    List.any_nil, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq,
    Minidregg.Pred.evalWith, hget, Option.some.injEq]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl Int.cast_zero
    · exact Or.inr Int.cast_one
  · rintro (hc | hc)
    · exact Or.inl (hinj x hx 0 h0 (by rw [hc]; exact Int.cast_zero.symm))
    · exact Or.inr (hinj x hx 1 h1 (by rw [hc]; exact Int.cast_one.symm))

end DecEqF

/-! ## §15. KEYSTONES — BUILT over `ZMod 7` and `ZMod 13` (ATLAS design-law 2 fields:
satisfiable + teeth + the general theorem firing on the instance), all `decide`d against
the REAL lowering fold — compiler, witness generator, and evaluator all kernel-computed. -/

instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- Keystone pre-state: `x = 3`, `z = 0` (`z` still writable: sentinel 0). -/
def kOld : State := ⟨[("x", 3), ("z", 0)]⟩

/-- Keystone post-state: `x = 5`, `y = 2`, `z = 4`. -/
def kNew : State := ⟨[("x", 5), ("y", 2), ("z", 4)]⟩

/-- A compound policy exercising every supported constructor: two atoms, membership,
write-once, negation, and the fail-closed `witnessed` under `not`. -/
def kPol : Pred :=
  Pred.all [.eq "y" 2, .memberOf "x" [1, 3, 5], .writeOnce "z",
            .not (.eq "x" 6), .not (.witnessed ⟨"vk"⟩)]

/-- A hostile post-state: `x = 6` violates BOTH the membership and the negated equality. -/
def kBad : State := ⟨[("x", 6), ("y", 2), ("z", 4)]⟩

-- The instance's cast label holds in both keystone fields (kernel-decided):
example : castInjOn (ZMod 7) (intsOf kPol kOld kNew) := by decide
example : castInjOn (ZMod 13) (intsOf kPol kOld kNew) := by decide

-- The fragment check and the source-level evaluations (kernel-decided):
example : supported kPol = true := by decide
example : Minidregg.Pred.eval kPol kOld kNew = true := by decide
example : Minidregg.Pred.eval kPol kOld kBad = false := by decide

/-- *Satisfiable, COMPUTED (ZMod 7)*: the compiled system accepts the emitted witness —
lowering fold, witness generator, and constraint evaluation all reduced in the kernel. -/
example : systemAccepts (stepAsg kOld kNew (wit kPol kOld kNew (F := ZMod 7)))
    (lower kPol) := by decide

/-- *Satisfiable, COMPUTED (ZMod 13)*: same pipeline, second field. -/
example : systemAccepts (stepAsg kOld kNew (wit kPol kOld kNew (F := ZMod 13)))
    (lower kPol) := by decide

/-- *The general theorem FIRES on the instance (ZMod 7)*: `lower_correct` (the ∀-predicate
refinement, not a bespoke argument) yields the acceptance from the source-level eval. -/
example : ∃ A : List ℕ → ℕ → ZMod 7,
    systemAccepts (stepAsg kOld kNew A) (lower kPol) :=
  (lower_correct (by decide) (by decide)).mpr (by decide)

/-- *Teeth via the general theorem (ZMod 7)*: on the hostile step NO aux assignment
whatsoever makes the compiled system accept — quantified over every prover strategy. -/
example : ¬ ∃ A : List ℕ → ℕ → ZMod 7,
    systemAccepts (stepAsg kOld kBad A) (lower kPol) := fun h => by
  have := (lower_correct (by decide) (by decide)).mp h
  simp [show Minidregg.Pred.eval kPol kOld kBad = false from by decide] at this

/-- *Teeth, COMPUTED (ZMod 13)*: the hostile step rejects even at the honest generator's
own aux values. -/
example : ¬ systemAccepts (stepAsg kOld kBad (wit kPol kOld kBad (F := ZMod 13)))
    (lower kPol) := by decide

/-- *Loud refusal, instantiated*: an order atom's lowering rejects everything (law 10 —
the unsupported leg is an unsatisfiable boundary, never silence). -/
example : ¬ systemAccepts (stepAsg kOld kNew (fun _ _ => (0 : ZMod 7)))
    (lower (.le "x" 9)) :=
  lower_le_refuses "x" 9 _

/-- *Fail-closed composition, COMPUTED*: `¬witnessed` is first-party TRUE and its
compilation accepts — the escape hatch's fail-closed indicator composes under negation. -/
example : systemAccepts
    (stepAsg kOld kNew (wit (.not (.witnessed ⟨"vk"⟩)) kOld kNew (F := ZMod 7)))
    (lower (.not (.witnessed ⟨"vk"⟩))) := by decide

/-- *Subsumption, instantiated (ZMod 7)*: on `kNew` (where `x = 5`), the compiled
booleanity POLICY and the hand `boolGadget` on the same value agree — here both REJECT
(`5` is not boolean), teeth on the subsumption face. -/
example : ¬ ∃ A : List ℕ → ℕ → ZMod 7,
    systemAccepts (stepAsg kOld kNew A) (lower (boolPol "x")) := fun h => by
  have := (lower_subsumes_boolGadget (x := 5) (by decide) (by decide)).mp h
  rw [boolGadget_correct] at this
  exact absurd this (by decide)

/-- A boolean-valued post-state for the accepting pole of the subsumption. -/
def kNewB : State := ⟨[("x", 1)]⟩

/-- *Subsumption, accepting pole (ZMod 7)*: `x = 1` — the compiled policy accepts, via the
subsumption iff, exactly because the hand gadget accepts `1`. -/
example : ∃ A : List ℕ → ℕ → ZMod 7,
    systemAccepts (stepAsg kOld kNewB A) (lower (boolPol "x")) :=
  (lower_subsumes_boolGadget (x := 1) (by decide) (by decide)).mpr
    (by rw [boolGadget_correct]; exact Or.inr rfl)

/-- info: 'Minidregg.Compiler.lower_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lower_correct
/-- info: 'Minidregg.Compiler.lower_subsumes_boolGadget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lower_subsumes_boolGadget

/-! ### Closing audit note

`lower_correct` is GENERAL: `lowerA_forced`/`lowerL_forced` and `lowerA_complete`/
`lowerL_complete` are mutual inductions with one arm per `Pred`/`PredList` constructor —
`eq`, `le`, `memberOf`, `writeOnce`, `monotone`, `witnessed`, `not`, `allL`, `anyL`, `nil`,
`cons` — none elided, no example-driven case. The keystones consume the theorem; they do
not constitute it. Residuals: `[PRED-COMPILE-order]` (the two order atoms, loudly
unsatisfiable until range-decomposed), `[PRED-COMPILE-oracle]` (oracle-discharged
`witnessed`), `[PRED-COMPILE-quant]` (no quantifiers in the source yet — widen `Pred`
first). The cast label `castInjOn` is a per-deployment parameter constraint, stated on
every theorem that needs it. Downstream: `lower`'s output is an `AirRange`
`ConstraintSystem`, so `AirFlatten`/`Emit` consume it unchanged — the policy-to-prover
path is compiler-authored end to end. -/

end Minidregg.Compiler
