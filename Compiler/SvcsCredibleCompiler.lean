/- Credible lowering of gate descriptors, bilinear contractions and lookup membership.
The checker replays an untrusted optimization trace with forward and backward witness maps.
The probabilistic theorem assumes uniform interactive challenges, honest terminal evaluations
and lookup membership. The native oracle verifier instantiates additional checks. -/
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Fin.Basic
import Selvage.MultilinearZeroTest
import Selvage.MultilinearExtension
import Selvage.SumcheckReduction
import Compiler.Emit
import Compiler.BabyBear
namespace Minidregg.Compiler.SvcsCredible
open Minidregg.Selvage

/-! ## §1. Linear forms and rows -/
section Core
variable {F : Type} [Field F]
/-- A linear form `Σ c·z_j` over the total witness vector (`z₀ = 1` carries constants). -/
abbrev LinForm (F : Type) := List (F × ℕ)
def lin (z : ℕ → F) : LinForm F → F
  | [] => 0
  | p :: f => p.1 * z p.2 + lin z f
@[simp] theorem lin_nil (z : ℕ → F) : lin z [] = 0 := rfl
@[simp] theorem lin_cons (z : ℕ → F) (p : F × ℕ) (f : LinForm F) :
    lin z (p :: f) = p.1 * z p.2 + lin z f := rfl
theorem lin_append (z : ℕ → F) (f g : LinForm F) : lin z (f ++ g) = lin z f + lin z g := by
  induction f with
  | nil => simp
  | cons p f ih => simp [ih, add_assoc]
def scale (c : F) (f : LinForm F) : LinForm F := f.map fun p => (c * p.1, p.2)
theorem lin_scale (z : ℕ → F) (c : F) (f : LinForm F) : lin z (scale c f) = c * lin z f := by
  induction f with
  | nil => simp [scale]
  | cons p f ih =>
    simp only [scale, List.map_cons, lin_cons] at *
    rw [ih]; ring
def renameF (ρ : ℕ → ℕ) (f : LinForm F) : LinForm F := f.map fun p => (p.1, ρ p.2)
theorem lin_renameF (z : ℕ → F) (ρ : ℕ → ℕ) (f : LinForm F) :
    lin z (renameF ρ f) = lin (fun i => z (ρ i)) f := by
  induction f with
  | nil => rfl
  | cons p f ih =>
    simp only [renameF, List.map_cons, lin_cons] at *
    rw [ih]
theorem lin_congr {z z' : ℕ → F} {f : LinForm F} (h : ∀ p ∈ f, z p.2 = z' p.2) :
    lin z f = lin z' f := by
  induction f with
  | nil => rfl
  | cons p f ih =>
    simp only [lin_cons]
    rw [h p List.mem_cons_self, ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
/-- Total coefficient of wire `t` in a form. -/
def coefW (t : ℕ) : LinForm F → F
  | [] => 0
  | p :: f => (if p.2 = t then p.1 else 0) + coefW t f
/-- The form with every `t`-term removed. -/
def dropW (t : ℕ) : LinForm F → LinForm F
  | [] => []
  | p :: f => if p.2 = t then dropW t f else p :: dropW t f
theorem lin_split (z : ℕ → F) (t : ℕ) (f : LinForm F) :
    lin z f = coefW t f * z t + lin z (dropW t f) := by
  induction f with
  | nil => simp [coefW, dropW]
  | cons p f ih =>
    by_cases h : p.2 = t
    · simp [coefW, dropW, h, ih]; ring
    · simp only [lin_cons, coefW, dropW, ite_eq_right h, ih]; ring

omit [Field F] in
theorem ne_of_mem_dropW (t : ℕ) (f : LinForm F) : ∀ p ∈ dropW t f, p.2 ≠ t := by
  induction f with
  | nil => simp [dropW]
  | cons p f ih =>
    intro q hq
    by_cases h : p.2 = t
    · rw [dropW, ite_eq_left h] at hq; exact ih q hq
    · rw [dropW, ite_eq_right h] at hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h
      · exact ih q hq
/-- A degree-2 sum-of-products row: `Σ_t ⟨a_t,z⟩·⟨b_t,z⟩ + ⟨c,z⟩ = 0`. -/
structure Row (F : Type) where
  prods : List (LinForm F × LinForm F)
  c : LinForm F
deriving DecidableEq
def prodSum (z : ℕ → F) : List (LinForm F × LinForm F) → F
  | [] => 0
  | ab :: ps => lin z ab.1 * lin z ab.2 + prodSum z ps

theorem prodSum_eq_sum (z : ℕ → F) (ps : List (LinForm F × LinForm F)) :
    prodSum z ps = (ps.map fun ab => lin z ab.1 * lin z ab.2).sum := by
  induction ps with
  | nil => rfl
  | cons ab ps ih => simp [prodSum, ih]
def Row.resid (z : ℕ → F) (r : Row F) : F := prodSum z r.prods + lin z r.c
def formWires (f : LinForm F) : List ℕ := f.map Prod.snd
def Row.wires (r : Row F) : List ℕ :=
  (r.prods.flatMap fun ab => formWires ab.1 ++ formWires ab.2) ++ formWires r.c
theorem Row.resid_congr {z z' : ℕ → F} {r : Row F} (h : ∀ j ∈ r.wires, z j = z' j) :
    r.resid z = r.resid z' := by
  have hp : ∀ ab ∈ r.prods, (∀ p ∈ ab.1, z p.2 = z' p.2) ∧ (∀ p ∈ ab.2, z p.2 = z' p.2) :=
    fun ab hab => ⟨fun p hp => h _ (List.mem_append_left _ (List.mem_flatMap.2
        ⟨ab, hab, List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩)⟩)),
      fun p hp => h _ (List.mem_append_left _ (List.mem_flatMap.2
        ⟨ab, hab, List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩)⟩))⟩
  have hc : ∀ p ∈ r.c, z p.2 = z' p.2 :=
    fun p hp => h _ (List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩))
  unfold Row.resid
  rw [lin_congr hc]
  congr 1
  rw [prodSum_eq_sum, prodSum_eq_sum]
  exact congrArg List.sum (List.map_congr_left fun ab hab => by
    rw [lin_congr (hp ab hab).1, lin_congr (hp ab hab).2])
def Row.rename (ρ : ℕ → ℕ) (r : Row F) : Row F :=
  ⟨r.prods.map fun ab => (renameF ρ ab.1, renameF ρ ab.2), renameF ρ r.c⟩

theorem Row.resid_rename (z : ℕ → F) (ρ : ℕ → ℕ) (r : Row F) :
    (r.rename ρ).resid z = r.resid (fun i => z (ρ i)) := by
  simp only [Row.rename, Row.resid, prodSum_eq_sum, List.map_map, Function.comp_def,
    lin_renameF]
/-- A lookup claim: every wire in `f` takes a value in `table`. (LogUp is how the engine proves it;
the relation here is membership.) -/
structure LookupClaim (F : Type) where
  f : List ℕ
  table : List F
deriving DecidableEq
/-- **The SVCS instance** (sum-check input statement): witness length, rows, lookup claims. -/
structure SvcsInstance (F : Type) where
  nZ : ℕ
  rows : List (Row F)
  lookups : List (LookupClaim F)
deriving DecidableEq
def SvcsInstance.Satisfied (s : SvcsInstance F) (z : ℕ → F) : Prop :=
  z 0 = 1 ∧ (∀ r ∈ s.rows, r.resid z = 0) ∧ ∀ l ∈ s.lookups, ∀ i ∈ l.f, z i ∈ l.table
instance [DecidableEq F] (s : SvcsInstance F) (z : ℕ → F) : Decidable (s.Satisfied z) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def SvcsInstance.wires (s : SvcsInstance F) : List ℕ :=
  s.rows.flatMap Row.wires ++ s.lookups.flatMap LookupClaim.f

/-! ## §2. The front-end IR -/
/-- Front items: Emit gate/zero/pin records, a bilinear contraction `C = A·B` (row-major blocks at
wire offsets `a, b, c`, shapes `m×k`, `k×n`), and a table lookup. -/
inductive FrontItem (F : Type) where
  | gate (g : DGate F)
  | zero (d : DWire F)
  | pin (i : ℕ) (v : F)
  | matmul (m k n a b c : ℕ)
  | lookup (i : ℕ) (table : List F)
deriving DecidableEq
def mmSum (w : ℕ → F) (k n a b i j : ℕ) : F :=
  ((List.range k).map fun l => w (a + i * k + l) * w (b + l * n + j)).sum
def FrontItem.holds (w : ℕ → F) : FrontItem F → Prop
  | .gate g => g.holds w
  | .zero d => d.read w = 0
  | .pin i v => w i = v
  | .matmul m k n a b c => ∀ i < m, ∀ j < n, w (c + i * n + j) = mmSum w k n a b i j
  | .lookup i T => w i ∈ T
instance [DecidableEq F] (w : ℕ → F) : (it : FrontItem F) → Decidable (it.holds w)
  | .gate g => inferInstanceAs (Decidable (g.holds w))
  | .zero d => inferInstanceAs (Decidable (d.read w = 0))
  | .pin i v => inferInstanceAs (Decidable (w i = v))
  | .matmul m k n a b c =>
    inferInstanceAs (Decidable (∀ i < m, ∀ j < n, w (c + i * n + j) = mmSum w k n a b i j))
  | .lookup i T => inferInstanceAs (Decidable (w i ∈ T))
structure FrontSpec (F : Type) where
  nWires : ℕ
  items : List (FrontItem F)
def FrontSpec.Holds (spec : FrontSpec F) (w : ℕ → F) : Prop := ∀ it ∈ spec.items, it.holds w
instance [DecidableEq F] (spec : FrontSpec F) (w : ℕ → F) : Decidable (spec.Holds w) :=
  inferInstanceAs (Decidable (∀ it ∈ spec.items, it.holds w))
/-- Embed an Emit `ConstraintDescriptor` (gates + zero-checked wires). -/
def FrontSpec.ofDescriptor (d : ConstraintDescriptor F) : FrontSpec F :=
  ⟨d.nWires, d.gates.map .gate ++ d.zeros.map .zero⟩

theorem ofDescriptor_holds_iff (d : ConstraintDescriptor F) (w : ℕ → F) :
    (FrontSpec.ofDescriptor d).Holds w ↔ descriptorHolds d w := by
  simp only [FrontSpec.ofDescriptor, FrontSpec.Holds, descriptorHolds, List.mem_append,
    List.mem_map, or_imp, forall_and]
  constructor
  · rintro ⟨hg, hz⟩
    exact ⟨fun g hg' => hg _ ⟨g, hg', rfl⟩, fun z hz' => hz _ ⟨z, hz', rfl⟩⟩
  · rintro ⟨hg, hz⟩
    exact ⟨by rintro _ ⟨g, hg', rfl⟩; exact hg g hg', by rintro _ ⟨z, hz', rfl⟩; exact hz z hz'⟩

/-! ## §3. The reference lowering (proved both ways) -/
def wireForm : DWire F → LinForm F
  | .cnst c => [(c, 0)]
  | .wire n => [(1, n + 1)]
def shiftW (z : ℕ → F) : ℕ → F := fun i => z (i + 1)
theorem lin_wireForm {z : ℕ → F} (hz : z 0 = 1) (d : DWire F) :
    lin z (wireForm d) = d.read (shiftW z) := by
  cases d <;> simp [wireForm, DWire.read, shiftW, hz]
def outForm (o : ℕ) : LinForm F := [(-1, o + 1)]
theorem lin_outForm (z : ℕ → F) (o : ℕ) : lin z (outForm o : LinForm F) = -shiftW z o := by
  simp [outForm, shiftW]
/-- Gate lowering. A multiplication by a constant lowers to a LINEAR row (fusable). -/
def gateRow (g : DGate F) : Row F :=
  match g.op, g.a, g.b with
  | .add, a, b => ⟨[], wireForm a ++ wireForm b ++ outForm g.out⟩
  | .mul, .cnst c, b => ⟨[], scale c (wireForm b) ++ outForm g.out⟩
  | .mul, .wire n, .cnst c => ⟨[], scale c (wireForm (.wire n)) ++ outForm g.out⟩
  | .mul, .wire n, .wire n' => ⟨[(wireForm (.wire n), wireForm (.wire n'))], outForm g.out⟩

theorem gateRow_resid {z : ℕ → F} (hz : z 0 = 1) (g : DGate F) :
    (gateRow g).resid z
      = g.op.denote (g.a.read (shiftW z)) (g.b.read (shiftW z)) - shiftW z g.out := by
  obtain ⟨op, a, b, o⟩ := g
  cases op <;> cases a <;> cases b <;>
    simp [gateRow, Row.resid, prodSum, lin_append, lin_scale, lin_wireForm hz, lin_outForm,
      GateOp.denote, DWire.read] <;> ring
def mmRow (k n a b c i j : ℕ) : Row F :=
  ⟨(List.range k).map fun l => ([((1 : F), a + i * k + l + 1)], [((1 : F), b + l * n + j + 1)]),
    outForm (c + i * n + j)⟩

theorem mmRow_resid (z : ℕ → F) (k n a b c i j : ℕ) :
    (mmRow k n a b c i j : Row F).resid z
      = mmSum (shiftW z) k n a b i j - shiftW z (c + i * n + j) := by
  simp [mmRow, Row.resid, prodSum_eq_sum, mmSum, lin_outForm, Function.comp_def, shiftW,
    sub_eq_add_neg]
def itemRows : FrontItem F → List (Row F)
  | .gate g => [gateRow g]
  | .zero d => [⟨[], wireForm d⟩]
  | .pin i v => [⟨[], [((1 : F), i + 1), (-v, 0)]⟩]
  | .matmul m k n a b c =>
    (List.range m).flatMap fun i => (List.range n).map fun j => mmRow k n a b c i j
  | .lookup _ _ => []
def itemLookups : FrontItem F → List (LookupClaim F)
  | .lookup i T => [⟨[i + 1], T⟩]
  | _ => []
/-- The reference lowering: front wire `i` ↦ SVCS wire `i+1`, `z₀ = 1`. -/
def lowerRef (spec : FrontSpec F) : SvcsInstance F :=
  ⟨spec.nWires + 1, spec.items.flatMap itemRows, spec.items.flatMap itemLookups⟩

theorem item_iff {z : ℕ → F} (hz : z 0 = 1) (it : FrontItem F) :
    ((∀ r ∈ itemRows it, r.resid z = 0) ∧ ∀ l ∈ itemLookups it, ∀ i ∈ l.f, z i ∈ l.table)
      ↔ it.holds (shiftW z) := by
  cases it with
  | gate g =>
    simp [itemRows, itemLookups, FrontItem.holds, DGate.holds, gateRow_resid hz, sub_eq_zero]
  | zero d => simp [itemRows, itemLookups, FrontItem.holds, Row.resid, prodSum, lin_wireForm hz]
  | pin i v =>
    simp [itemRows, itemLookups, FrontItem.holds, Row.resid, prodSum, hz, shiftW,
      add_neg_eq_zero]
  | matmul m k n a b c =>
    simp only [itemRows, itemLookups, FrontItem.holds, List.mem_flatMap, List.mem_map,
      List.mem_range, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
    constructor
    · intro h i hi j hj
      have := h _ ⟨i, hi, j, hj, rfl⟩
      rw [mmRow_resid] at this
      exact (sub_eq_zero.1 this).symm
    · rintro h r ⟨i, hi, j, hj, rfl⟩
      rw [mmRow_resid, h i hi j hj, sub_self]
  | lookup i T => simp [itemRows, itemLookups, FrontItem.holds, shiftW]

theorem lowerRef_sat_iff (spec : FrontSpec F) {z : ℕ → F} (hz : z 0 = 1) :
    (lowerRef spec).Satisfied z ↔ spec.Holds (shiftW z) := by
  simp only [SvcsInstance.Satisfied, lowerRef, FrontSpec.Holds, List.mem_flatMap]
  constructor
  · rintro ⟨_, hr, hl⟩ it hit
    exact (item_iff hz it).1 ⟨fun r hr' => hr r ⟨it, hit, hr'⟩, fun l hl' => hl l ⟨it, hit, hl'⟩⟩
  · intro h
    refine ⟨hz, ?_, ?_⟩
    · rintro r ⟨it, hit, hr⟩; exact ((item_iff hz it).2 (h it hit)).1 r hr
    · rintro l ⟨it, hit, hl⟩; exact ((item_iff hz it).2 (h it hit)).2 l hl
/-- The forward embedding of a front witness: `z₀ = 1`, `z_{i+1} = w_i`. -/
def embed (w : ℕ → F) : ℕ → F
  | 0 => 1
  | i + 1 => w i

/-! ## §4. Optimization steps, each with its own witness maps -/
variable [DecidableEq F]
inductive Step (F : Type) where
  | dce (keep : List ℕ)
  | fuse (r1 r2 : Row F) (t : ℕ)
  | dedupClaims
deriving DecidableEq
def renameInst (ρ : ℕ → ℕ) (n : ℕ) (s : SvcsInstance F) : SvcsInstance F :=
  ⟨n, s.rows.map (Row.rename ρ), s.lookups.map fun l => ⟨l.f.map ρ, l.table⟩⟩
/-- The fused row: `β·(r1.c − α t) − α·(r2.c − β t)`; the intermediate wire `t` cancels. -/
def fusedRow (r1 r2 : Row F) (t : ℕ) : Row F :=
  ⟨[], scale (coefW t r2.c) (dropW t r1.c) ++ scale (-coefW t r1.c) (dropW t r2.c)⟩
/-- Fusion guard: both rows LINEAR (degree preservation), `t`'s pivot nonzero, `t ≠ 0`, and `t`
occurs in no other row and no lookup. -/
def FuseOk (s : SvcsInstance F) (r1 r2 : Row F) (t : ℕ) : Prop :=
  r1 ∈ s.rows ∧ r2 ∈ s.rows ∧ r1.prods = [] ∧ r2.prods = [] ∧ coefW t r1.c ≠ 0 ∧ t ≠ 0 ∧
    (∀ r ∈ s.rows, r ≠ r1 → r ≠ r2 → t ∉ r.wires) ∧ ∀ l ∈ s.lookups, t ∉ l.f
instance (s : SvcsInstance F) (r1 r2 : Row F) (t : ℕ) : Decidable (FuseOk s r1 r2 t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
def fuseInst (s : SvcsInstance F) (r1 r2 : Row F) (t : ℕ) : SvcsInstance F :=
  ⟨s.nZ, fusedRow r1 r2 t :: s.rows.filter (fun r => r != r1 && r != r2), s.lookups⟩
def DceOk (s : SvcsInstance F) (keep : List ℕ) : Prop :=
  keep.head? = some 0 ∧ ∀ j ∈ s.wires, j ∈ keep
instance (s : SvcsInstance F) (keep : List ℕ) : Decidable (DceOk s keep) :=
  inferInstanceAs (Decidable (_ ∧ _))
def Step.apply : Step F → SvcsInstance F → Option (SvcsInstance F)
  | .dce keep, s => if DceOk s keep then some (renameInst keep.idxOf keep.length s) else none
  | .fuse r1 r2 t, s => if FuseOk s r1 r2 t then some (fuseInst s r1 r2 t) else none
  | .dedupClaims, s => some ⟨s.nZ, s.rows.dedup, s.lookups⟩
/-- Backward (extraction) map: new SVCS witness ↦ old SVCS witness. -/
def Step.back : Step F → (ℕ → F) → ℕ → F
  | .dce keep, z => fun i => z (keep.idxOf i)
  | .fuse r1 _ t, z => fun i => if i = t then -(lin z (dropW t r1.c)) / coefW t r1.c else z i
  | .dedupClaims, z => z
/-- Forward (completeness) map: old SVCS witness ↦ new SVCS witness. -/
def Step.fwd : Step F → (ℕ → F) → ℕ → F
  | .dce keep, z => fun j => z (keep.getD j 0)
  | .fuse _ _ _, z => z
  | .dedupClaims, z => z

theorem head_zero_idxOf {keep : List ℕ} (h : keep.head? = some 0) : keep.idxOf 0 = 0 := by
  cases keep with
  | nil => simp at h
  | cons a tl => simp only [List.head?_cons, Option.some.injEq] at h; subst h; simp

theorem step_sound {st : Step F} {s s' : SvcsInstance F} (h : st.apply s = some s')
    {z : ℕ → F} (hz : s'.Satisfied z) : s.Satisfied (st.back z) := by
  cases st with
  | dce keep =>
    simp only [Step.apply] at h
    split_ifs at h with hok
    cases h
    obtain ⟨hz0, hr, hl⟩ := hz
    refine ⟨by simp only [Step.back]; rw [head_zero_idxOf hok.1]; exact hz0, ?_, ?_⟩
    · intro r hrm
      have := hr _ (List.mem_map.2 ⟨r, hrm, rfl⟩)
      rwa [Row.resid_rename] at this
    · intro l hlm i hi
      exact hl _ (List.mem_map.2 ⟨l, hlm, rfl⟩) _ (List.mem_map.2 ⟨i, hi, rfl⟩)
  | fuse r1 r2 t =>
    simp only [Step.apply] at h
    split_ifs at h with hok
    cases h
    obtain ⟨h1, h2, hp1, hp2, hα, ht0, hother, hlk⟩ := hok
    obtain ⟨hz0, hr, hl⟩ := hz
    set α := coefW t r1.c
    set z' := Function.update z t (-(lin z (dropW t r1.c)) / α)
    rw [show (Step.fuse r1 r2 t).back z = z' from funext fun i => (Function.update_apply z t _ i).symm]
    have hoff : ∀ f : LinForm F, (∀ p ∈ f, p.2 ≠ t) → lin z' f = lin z f :=
      fun f hf => lin_congr fun p hp => Function.update_of_ne (hf p hp) _ _
    have hzt : z' t = -(lin z (dropW t r1.c)) / α := Function.update_self _ _ _
    have hfus := hr _ List.mem_cons_self
    simp only [fusedRow, Row.resid, prodSum, lin_append, lin_scale, zero_add] at hfus
    have key : ∀ r : Row F, r.prods = [] → r.resid z' = coefW t r.c * z' t + lin z (dropW t r.c) :=
      fun r hpr => by
        rw [Row.resid, hpr, prodSum, zero_add, lin_split z' t r.c,
          hoff _ (ne_of_mem_dropW t r.c)]
    refine ⟨(Function.update_of_ne (Ne.symm ht0) _ z).trans hz0, ?_, ?_⟩
    · intro r hrm
      show r.resid z' = 0
      by_cases e1 : r = r1
      · subst e1; rw [key r hp1, hzt]; field_simp; ring
      by_cases e2 : r = r2
      · subst e2
        rw [key r hp2, hzt]
        field_simp
        dsimp [α]; linear_combination -hfus
      have hkeep := hr r (List.mem_cons_of_mem _ (List.mem_filter.2 ⟨hrm, by simp [e1, e2]⟩))
      rw [← hkeep]
      exact Row.resid_congr fun j hj => Function.update_of_ne
        (fun (hjt : j = t) => hother r hrm e1 e2 (hjt ▸ hj)) _ _
    · intro l hlm i hi
      show z' i ∈ l.table
      rw [show z' i = z i from Function.update_of_ne (fun (hit : i = t) => hlk l hlm (hit ▸ hi)) _ _]
      exact hl l hlm i hi
  | dedupClaims =>
    simp only [Step.apply, Option.some.injEq] at h
    subst h
    obtain ⟨hz0, hr, hl⟩ := hz
    exact ⟨hz0, fun r hrm => hr r (List.mem_dedup.2 hrm), hl⟩

theorem step_complete {st : Step F} {s s' : SvcsInstance F} (h : st.apply s = some s')
    {z : ℕ → F} (hz : s.Satisfied z) : s'.Satisfied (st.fwd z) := by
  cases st with
  | dce keep =>
    simp only [Step.apply] at h
    split_ifs at h with hok
    cases h
    obtain ⟨hhead, hall⟩ := hok
    obtain ⟨hz0, hr, hl⟩ := hz
    have hgi : ∀ j ∈ s.wires, keep.getD (keep.idxOf j) 0 = j := fun j hj => by
      rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem (hall j hj))]
      exact List.getElem_idxOf _
    refine ⟨?_, ?_, ?_⟩
    · cases keep with
      | nil => simp at hhead
      | cons a tl =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead; exact hz0
    · intro r' hr'
      obtain ⟨r, hrm, rfl⟩ := List.mem_map.1 hr'
      simp only [Step.fwd, Row.resid_rename]
      rw [← hr r hrm]
      exact Row.resid_congr fun j hj => by
        rw [hgi j (List.mem_append_left _ (List.mem_flatMap.2 ⟨r, hrm, hj⟩))]
    · intro l' hl' i' hi'
      obtain ⟨l, hlm, rfl⟩ := List.mem_map.1 hl'
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hi'
      simp only [Step.fwd]
      rw [hgi i (List.mem_append_right _ (List.mem_flatMap.2 ⟨l, hlm, hi⟩))]
      exact hl l hlm i hi
  | fuse r1 r2 t =>
    simp only [Step.apply] at h
    split_ifs at h with hok
    cases h
    obtain ⟨h1, h2, hp1, hp2, -, -, -, -⟩ := hok
    obtain ⟨hz0, hr, hl⟩ := hz
    refine ⟨hz0, ?_, hl⟩
    intro r hrm
    rcases List.mem_cons.1 hrm with rfl | hrm
    · have e1 := hr r1 h1
      have e2 := hr r2 h2
      rw [Row.resid, hp1, prodSum, zero_add, lin_split z t] at e1
      rw [Row.resid, hp2, prodSum, zero_add, lin_split z t] at e2
      simp only [Step.fwd, fusedRow, Row.resid, prodSum, lin_append, lin_scale, zero_add]
      linear_combination coefW t r2.c * e1 - coefW t r1.c * e2
    · exact hr r (List.mem_filter.1 hrm).1
  | dedupClaims =>
    simp only [Step.apply, Option.some.injEq] at h
    subst h
    obtain ⟨hz0, hr, hl⟩ := hz
    exact ⟨hz0, fun r hrm => hr r (List.mem_dedup.1 hrm), hl⟩
def replay : SvcsInstance F → List (Step F) → Option (SvcsInstance F)
  | s, [] => some s
  | s, st :: sts => (st.apply s).bind fun s' => replay s' sts
def backAll : List (Step F) → (ℕ → F) → ℕ → F
  | [], z => z
  | st :: sts, z => st.back (backAll sts z)
def fwdAll : List (Step F) → (ℕ → F) → ℕ → F
  | [], z => z
  | st :: sts, z => fwdAll sts (st.fwd z)

theorem replay_sound : ∀ {sts : List (Step F)} {s s' : SvcsInstance F},
    replay s sts = some s' → ∀ {z}, s'.Satisfied z → s.Satisfied (backAll sts z)
  | [], s, s', h, z, hz => by
    simp only [replay, Option.some.injEq] at h; subst h; exact hz
  | st :: sts, s, s', h, z, hz => by
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨s1, h1, h2⟩ := h
    exact step_sound h1 (replay_sound h2 hz)

theorem replay_complete : ∀ {sts : List (Step F)} {s s' : SvcsInstance F},
    replay s sts = some s' → ∀ {z}, s.Satisfied z → s'.Satisfied (fwdAll sts z)
  | [], s, s', h, z, hz => by
    simp only [replay, Option.some.injEq] at h; subst h; exact hz
  | st :: sts, s, s', h, z, hz => by
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨s1, h1, h2⟩ := h
    exact replay_complete h2 (step_complete h1 hz)

/-! ## §5. Lanes, the certificate, the checker, and the keystones -/
inductive Lane | u8 | i8 | i16 | u32
deriving DecidableEq, Repr
def Lane.name : Lane → String
  | .u8 => "u8" | .i8 => "i8" | .i16 => "i16" | .u32 => "u32"
/-- What a lane tag means for a field element (BabyBear: the canonical-integer reading). -/
class LaneSemantics (F : Type) where
  laneOk : Lane → F → Bool
def tagsJustified [LaneSemantics F] (s : SvcsInstance F) (tags : List (ℕ × Lane)) : Bool :=
  tags.all fun jl => s.lookups.any fun l =>
    decide (jl.1 ∈ l.f) && l.table.all (LaneSemantics.laneOk jl.2)
omit [DecidableEq F] in
/-- Each justified lane contains the value of its wire in every satisfying witness. -/
theorem tags_sound [LaneSemantics F] {s : SvcsInstance F} {tags : List (ℕ × Lane)}
    (ht : tagsJustified s tags = true) {z : ℕ → F} (hz : s.Satisfied z) :
    ∀ jl ∈ tags, LaneSemantics.laneOk jl.2 (z jl.1) = true := by
  intro jl hjl
  simp only [tagsJustified, List.all_eq_true, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at ht
  obtain ⟨l, hl, hj, htab⟩ := ht jl hjl
  exact htab _ (hz.2.2 l hl jl.1 hj)
def wfB (s : SvcsInstance F) : Bool := decide (0 < s.nZ) && s.wires.all (· < s.nZ)
structure CredibleLoweringCert (F : Type) where
  steps : List (Step F)
  tags : List (ℕ × Lane)
def CredibleLoweringCert.extractWitness (c : CredibleLoweringCert F) (z : ℕ → F) : ℕ → F :=
  shiftW (backAll c.steps z)
def CredibleLoweringCert.forwardWitness (c : CredibleLoweringCert F) (w : ℕ → F) : ℕ → F :=
  fwdAll c.steps (embed w)
/-- **The total checker.** Replay the certified steps from the reference lowering, validating each;
the result must BE the claimed instance; tags must be justified; wires in range. -/
def checkCredibleCert [LaneSemantics F] (spec : FrontSpec F) (svcs : SvcsInstance F)
    (cert : CredibleLoweringCert F) : Bool :=
  match replay (lowerRef spec) cert.steps with
  | some s => decide (s = svcs) && tagsJustified svcs cert.tags && wfB svcs
  | none => false

theorem checkCredibleCert_spec [LaneSemantics F] {spec : FrontSpec F} {svcs : SvcsInstance F}
    {cert : CredibleLoweringCert F} (h : checkCredibleCert spec svcs cert = true) :
    replay (lowerRef spec) cert.steps = some svcs ∧ tagsJustified svcs cert.tags = true := by
  unfold checkCredibleCert at h
  cases hr : replay (lowerRef spec) cert.steps with
  | none => simp [hr] at h
  | some s =>
    simp only [hr, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, ht⟩, -⟩ := h
    exact ⟨rfl, ht⟩
/-- **Completeness.** A front witness maps forward to a satisfying SVCS witness. -/
theorem credible_cert_completeness [LaneSemantics F] {spec : FrontSpec F}
    {svcs : SvcsInstance F} {cert : CredibleLoweringCert F}
    (h : checkCredibleCert spec svcs cert = true) {w : ℕ → F} (hw : spec.Holds w) :
    svcs.Satisfied (cert.forwardWitness w) :=
  replay_complete (checkCredibleCert_spec h).1
    ((lowerRef_sat_iff spec (z := embed w) rfl).2 hw)
/-- **Knowledge soundness.** Any satisfying SVCS witness extracts to a front witness. -/
theorem credible_cert_knowledge_soundness [LaneSemantics F] {spec : FrontSpec F}
    {svcs : SvcsInstance F} {cert : CredibleLoweringCert F}
    (h : checkCredibleCert spec svcs cert = true) {z : ℕ → F} (hz : svcs.Satisfied z) :
    spec.Holds (cert.extractWitness z) := by
  have h0 := replay_sound (checkCredibleCert_spec h).1 hz
  exact (lowerRef_sat_iff spec h0.1).1 h0
/-- The Emit corollary: an accepted certificate for an embedded descriptor extracts a wire vector
satisfying the emitted descriptor. -/
theorem credible_emit_knowledge_soundness [LaneSemantics F] {d : ConstraintDescriptor F}
    {svcs : SvcsInstance F} {cert : CredibleLoweringCert F}
    (h : checkCredibleCert (FrontSpec.ofDescriptor d) svcs cert = true) {z : ℕ → F}
    (hz : svcs.Satisfied z) : descriptorHolds d (cert.extractWitness z) :=
  (ofDescriptor_holds_iff d _).1 (credible_cert_knowledge_soundness h hz)
theorem credible_emit_accepts {Idx : Type} [LaneSemantics F] (ix : Idx → ℕ)
    (hinj : Function.Injective ix) (np nv : ℕ) (hb : ∀ i, ix i < nv)
    (asg : Idx → F) (sys : ConstraintSystem F Idx) {svcs : SvcsInstance F}
    {c : CredibleLoweringCert F} {z : ℕ → F}
    (hc : checkCredibleCert (FrontSpec.ofDescriptor (emit ix np nv sys)) svcs c = true)
    (hz : svcs.Satisfied z) (hp : ∀ i, c.extractWitness z (ix i) = asg i) : systemAccepts asg sys :=
  (emit_accepts_iff ix hinj np nv hb asg sys).1 ⟨_, hp, credible_emit_knowledge_soundness hc hz⟩

/-! ## §6. The untrusted cost-guided optimizer -/
/-- Cost proxy (prover work units): 4 per committed column cell, 8 per product term plus form
lengths per row (extension multiplies in the zerocheck), lookups by length. -/
def SvcsInstance.cost (s : SvcsInstance F) : ℕ :=
  4 * s.nZ + (s.rows.map fun r => 8 * r.prods.length
      + (r.prods.map fun ab => ab.1.length + ab.2.length).sum + r.c.length + 2).sum
    + (s.lookups.map fun l => 3 * l.f.length + l.table.length).sum
def fuseCandidate (s : SvcsInstance F) (t : ℕ) : Option (Step F) :=
  if t = 0 ∨ s.lookups.any (fun l => decide (t ∈ l.f)) then none else
  match s.rows.filter (fun r => decide (t ∈ r.wires)) with
  | [r1, r2] => if r1.prods = [] ∧ r2.prods = [] ∧ coefW t r1.c ≠ 0 then some (.fuse r1 r2 t)
    else none
  | _ => none
abbrev CostModel (F : Type) := SvcsInstance F → ℕ
def improving (score : CostModel F) (s : SvcsInstance F) (st : Step F) : Option (Step F × SvcsInstance F) := do
  let next ← st.apply s
  guard (score next < score s)
  return (st, next)
def optimizeLoop (score : CostModel F) : ℕ → SvcsInstance F → List (Step F) → List (Step F)
  | 0, _, acc => acc
  | fuel + 1, s, acc =>
    match s.wires.dedup.findSome? (fun t => (fuseCandidate s t).bind (improving score s)) with
    | some (st, next) => optimizeLoop score fuel next (acc ++ [st])
    | none => acc
def inferTags [LaneSemantics F] (s : SvcsInstance F) : List (ℕ × Lane) :=
  (List.range s.nZ).filterMap fun j =>
    ([Lane.u8, Lane.i8, Lane.i16].find? fun ℓ => s.lookups.any fun l =>
      decide (j ∈ l.f) && l.table.all (LaneSemantics.laneOk ℓ)).map ((j, ·))
def optimize (s0 : SvcsInstance F) (score : CostModel F := SvcsInstance.cost) : List (Step F) :=
  let fuses := optimizeLoop score s0.rows.length s0 []
  let s1 := ((replay s0 fuses).getD s0)
  let dce := Step.dce ((List.range s1.nZ).filter fun j => j = 0 ∨ j ∈ s1.wires)
  fuses ++ (([Step.dedupClaims, dce] : List (Step F)).foldl (fun (acc, s) st =>
    match improving score s st with | some (_, next) => (acc ++ [st], next) | none => (acc, s))
    ([], s1)).1
def compile [LaneSemantics F] (spec : FrontSpec F) (score : CostModel F := SvcsInstance.cost) : SvcsInstance F × CredibleLoweringCert F :=
  let s0 := lowerRef spec
  let steps := optimize s0 score
  let s := (replay s0 steps).getD s0
  (s, ⟨steps, inferTags s⟩)
end Core

/-! ## §7. Composition with the Selvage zero-test and adaptive sum-check -/
section Composed
variable {F : Type} [Field F] {m : ℕ}
open Polynomial
/-- The affine polynomial of `f` in coordinate `i` at base point `x`. -/
noncomputable def affPoly (f : (Fin m → F) → F) (x : Fin m → F) (i : Fin m) : F[X] :=
  C (f (Function.update x i 1) - f (Function.update x i 0)) * X + C (f (Function.update x i 0))
theorem affPoly_eval {f : (Fin m → F) → F} {i : Fin m} (hf : AffineInCoord f i) (x : Fin m → F)
    (t : F) : (affPoly f x i).eval t = f (Function.update x i t) := by
  rw [hf x t]; simp [affPoly]; ring
/-- Sum of products of factor functions: `Σ_q Π_{f∈q} f(x)`. -/
def sop (Q : List (List ((Fin m → F) → F))) (x : Fin m → F) : F :=
  (Q.map fun q => (q.map fun f => f x).prod).sum
noncomputable def sopPoly (Q : List (List ((Fin m → F) → F))) (x : Fin m → F) (i : Fin m) :
    F[X] := (Q.map fun q => (q.map fun f => affPoly f x i).prod).sum
theorem sopPoly_eval {Q : List (List ((Fin m → F) → F))} (hQ : ∀ q ∈ Q, ∀ f ∈ q, MultiAffine f)
    (x : Fin m → F) (i : Fin m) (t : F) :
    (sopPoly Q x i).eval t = sop Q (Function.update x i t) := by
  simp only [sopPoly, sop, Polynomial.eval_listSum, List.map_map, Function.comp_def,
    Polynomial.eval_list_prod]
  exact congrArg List.sum (List.map_congr_left fun q hq => congrArg List.prod
    (List.map_congr_left fun f hf => affPoly_eval (hQ q hq f hf i) x t))
theorem sopPoly_natDegree {Q : List (List ((Fin m → F) → F))} {d : ℕ}
    (hd : ∀ q ∈ Q, q.length ≤ d) (x : Fin m → F) (i : Fin m) : (sopPoly Q x i).natDegree ≤ d := by
  have hprod : ∀ q : List ((Fin m → F) → F),
      (q.map fun f => affPoly f x i).prod.natDegree ≤ q.length := by
    intro q
    induction q with
    | nil => simp
    | cons f q ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      refine (natDegree_mul_le).trans ?_
      have : (affPoly f x i).natDegree ≤ 1 := natDegree_linear_le
      omega
  induction Q with
  | nil => simp [sopPoly]
  | cons q Q ih =>
    simp only [sopPoly, List.map_cons, List.sum_cons] at *
    exact natDegree_add_le_of_degree_le
      ((hprod q).trans (hd q List.mem_cons_self))
      (ih fun q' hq' => hd q' (List.mem_cons_of_mem _ hq'))
/-- **The degree-`d` honest round family** for `g = sop Q`: round `i` sums the affine-product
polynomial over the boolean suffix. -/
noncomputable def sopHonest (Q : List (List ((Fin m → F) → F))) (χ : ℕ → F) (i : ℕ) : F[X] :=
  if h : i < m then
    ∑ b : SuffixCube m (i + 1), sopPoly Q (glue (fun j : Fin m => χ j.val) (i + 1) b) ⟨i, h⟩
  else 0
theorem sopHonest_eval {Q : List (List ((Fin m → F) → F))} (hQ : ∀ q ∈ Q, ∀ f ∈ q, MultiAffine f)
    (χ : ℕ → F) {i : ℕ} (h : i < m) (t : F) :
    (sopHonest Q χ i).eval t = roundSum (sop Q) (fun j : Fin m => χ j.val) ⟨i, h⟩ t := by
  rw [sopHonest, dite_eq_left h, Polynomial.eval_finsetSum, roundSum]
  exact Finset.sum_congr rfl fun b _ => by
    rw [sopPoly_eval hQ, glue_update (i := ⟨i, h⟩)]
theorem sopHonest_prefixMeasurable (Q : List (List ((Fin m → F) → F))) :
    PrefixMeasurable (sopHonest Q) := by
  intro χ χ' i hpre
  unfold sopHonest
  split_ifs with h
  · refine Finset.sum_congr rfl fun b _ => ?_
    have hupd : ∀ s : F, Function.update (glue (fun j : Fin m => χ j.val) (i + 1) b) ⟨i, h⟩ s
        = Function.update (glue (fun j : Fin m => χ' j.val) (i + 1) b) ⟨i, h⟩ s := by
      intro s; funext j
      rcases eq_or_ne j ⟨i, h⟩ with rfl | hne
      · simp
      · rw [Function.update_of_ne hne, Function.update_of_ne hne, glue_apply, glue_apply]
        split_ifs with hj
        · rfl
        · have hv : j.val ≠ i := fun hv => hne (Fin.ext hv)
          exact hpre j.val (by omega)
    simp only [sopPoly, affPoly, hupd]
  · rfl
theorem sopHonest_natDegree {Q : List (List ((Fin m → F) → F))} {d : ℕ}
    (hd : ∀ q ∈ Q, q.length ≤ d) (χ : ℕ → F) (i : ℕ) (_hi : i < m) :
    (sopHonest Q χ i).degree < ((d + 1 : ℕ) : WithBot ℕ) := by
  have : (sopHonest Q χ i).natDegree ≤ d := by
    rw [sopHonest, dite_eq_left _hi]; exact natDegree_sum_le_of_forall_le _ _ fun _ _ => sopPoly_natDegree hd _ _
  exact lt_of_le_of_lt (degree_le_of_natDegree_le this) (WithBot.coe_lt_coe.2 (Nat.lt_succ_self d))
theorem sopHonest_boolean_sum {Q : List (List ((Fin m → F) → F))}
    (hQ : ∀ q ∈ Q, ∀ f ∈ q, MultiAffine f) (r : Fin m → F) :
    ∀ i, i < m → (sopHonest Q (chalOf r) i).eval 0 + (sopHonest Q (chalOf r) i).eval 1
      = scChain (∑ b, sop Q (cubePt b)) (sopHonest Q (chalOf r)) (chalOf r) i := by
  intro i hi
  rw [sopHonest_eval hQ _ hi, sopHonest_eval hQ _ hi]
  cases i with
  | zero => exact roundSum_zero hi (sop Q) _
  | succ n =>
    show _ = (sopHonest Q (chalOf r) n).eval (chalOf r n)
    rw [sopHonest_eval hQ _ (Nat.lt_of_succ_lt hi)]
    exact roundSum_succ hi (sop Q) _
/-- The truth chain ends at the oracle evaluation `sop Q r` — for the zerocheck factors, exactly
`eq(τ,r)·(Σ_t ã_t(r)·b̃_t(r) + c̃(r))`, the claim the engine's verifier checks. -/
theorem sopHonest_final {Q : List (List ((Fin m → F) → F))}
    (hQ : ∀ q ∈ Q, ∀ f ∈ q, MultiAffine f) (r : Fin m → F) :
    scChain (∑ b, sop Q (cubePt b)) (sopHonest Q (chalOf r)) (chalOf r) m = sop Q r := by
  cases m with
  | zero =>
    show ∑ b, sop Q (cubePt b) = sop Q r
    rw [Fintype.sum_unique]
    exact congrArg _ (funext fun j => j.elim0)
  | succ n =>
    show (sopHonest Q (chalOf r) n).eval (chalOf r n) = sop Q r
    rw [sopHonest_eval hQ _ (Nat.lt_succ_self n), roundSum_last (by simp)]
    conv_rhs => rw [← chalOf_restrict r]
    exact congrArg _ (Function.update_eq_self _ _)

/-! The zerocheck tables of an SVCS instance on the boolean hypercube. -/
noncomputable def cubeIdx (m : ℕ) : (Fin m → Bool) ≃ Fin (2 ^ m) :=
  (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans finFunctionFinEquiv
def rowAt (s : SvcsInstance F) (k : ℕ) : Row F := s.rows.getD k ⟨[], []⟩
def prodAt (r : Row F) (t : ℕ) : LinForm F × LinForm F := r.prods.getD t ([], [])
noncomputable def tblA (s : SvcsInstance F) (z : ℕ → F) (t : ℕ) (b : Fin m → Bool) : F :=
  lin z (prodAt (rowAt s (cubeIdx m b)) t).1
noncomputable def tblB (s : SvcsInstance F) (z : ℕ → F) (t : ℕ) (b : Fin m → Bool) : F :=
  lin z (prodAt (rowAt s (cubeIdx m b)) t).2
noncomputable def tblC (s : SvcsInstance F) (z : ℕ → F) (b : Fin m → Bool) : F :=
  lin z (rowAt s (cubeIdx m b)).c
/-- The engine's zerocheck polynomial as factors:
`eq(τ,x)·(Σ_{t<T} ã_t(x)·b̃_t(x) + c̃(x))`. -/
noncomputable def zcFactors (s : SvcsInstance F) (z : ℕ → F) (τ : Fin m → F) (T : ℕ) :
    List (List ((Fin m → F) → F)) :=
  (List.range T).map (fun t => [eqMle τ, mle (tblA s z t), mle (tblB s z t)])
    ++ [[eqMle τ, mle (tblC s z)]]
theorem zcFactors_affine (s : SvcsInstance F) (z : ℕ → F) (τ : Fin m → F) (T : ℕ) :
    ∀ q ∈ zcFactors s z τ T, ∀ f ∈ q, MultiAffine f := by
  intro q hq f hf
  simp only [zcFactors, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hq
  rcases hq with ⟨t, -, rfl⟩ | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  · rcases hf with rfl | rfl | rfl <;> first | exact eqMle_multilinear _ | exact mle_multilinear _
  · rcases hf with rfl | rfl <;> first | exact eqMle_multilinear _ | exact mle_multilinear _
theorem zcFactors_length (s : SvcsInstance F) (z : ℕ → F) (τ : Fin m → F) (T : ℕ) :
    ∀ q ∈ zcFactors s z τ T, q.length ≤ 3 := by
  intro q hq
  simp only [zcFactors, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hq
  rcases hq with ⟨t, -, rfl⟩ | rfl <;> simp
theorem prodSum_getD (z : ℕ → F) : ∀ (ps : List (LinForm F × LinForm F)) (T : ℕ),
    ps.length ≤ T → ((List.range T).map fun t =>
      lin z (ps.getD t ([], [])).1 * lin z (ps.getD t ([], [])).2).sum = prodSum z ps
  | [], T, _ => by simp [prodSum]
  | ab :: ps, T + 1, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero]
    rw [prodSum_getD z ps T (by simpa using h), prodSum]
  | _ :: _, 0, h => by simp at h
theorem sop_zc_cube (s : SvcsInstance F) (z : ℕ → F) (τ : Fin m → F) {T : ℕ}
    (hT : ∀ r ∈ s.rows, r.prods.length ≤ T) (b : Fin m → Bool) :
    sop (zcFactors s z τ T) (cubePt b) = eqMle τ (cubePt b) * (rowAt s (cubeIdx m b)).resid z := by
  have hlen : (rowAt s (cubeIdx m b)).prods.length ≤ T := by
    unfold rowAt
    rcases lt_or_ge (cubeIdx m b : ℕ) s.rows.length with hk | hk
    · rw [List.getD_eq_getElem _ _ hk]; exact hT _ (List.getElem_mem hk)
    · rw [List.getD_eq_default _ _ hk]; exact Nat.zero_le _
  simp only [sop, zcFactors, List.map_append, List.map_map, Function.comp_def, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, List.sum_append, List.sum_cons,
    List.sum_nil, add_zero, mle_agrees]
  rw [Row.resid, ← prodSum_getD z _ T hlen, mul_add]
  rw [List.sum_map_mul_left]; rfl
theorem defect_witness (s : SvcsInstance F) (z : ℕ → F) (hm : s.rows.length ≤ 2 ^ m)
    {r : Row F} (hr : r ∈ s.rows) (hne : r.resid z ≠ 0) :
    ∃ b : Fin m → Bool, (rowAt s (cubeIdx m b)).resid z ≠ 0 := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  refine ⟨(cubeIdx m).symm ⟨k, lt_of_lt_of_le hk hm⟩, ?_⟩
  rw [Equiv.apply_symm_apply, rowAt, List.getD_eq_getElem _ _ hk]
  exact hne
/-- For a fixed normalized witness satisfying the lookups, false acceptance costs at most 4m/|F|. -/
theorem svcs_rbr_soundness_composed [Fintype F] [DecidableEq F] [LaneSemantics F] {spec : FrontSpec F}
    {svcs : SvcsInstance F} {cert : CredibleLoweringCert F}
    (hchk : checkCredibleCert spec svcs cert = true) {z : ℕ → F} (hz0 : z 0 = 1)
    (hlk : ∀ l ∈ svcs.lookups, ∀ i ∈ l.f, z i ∈ l.table)
    (hbad : ¬ spec.Holds (cert.extractWitness z))
    {T : ℕ} (hT : ∀ r ∈ svcs.rows, r.prods.length ≤ T) (hm : svcs.rows.length ≤ 2 ^ m)
    {prover : (Fin m → F) → (ℕ → F) → ℕ → F[X]} (hpm : ∀ τ, PrefixMeasurable (prover τ))
    (hdeg : ∀ τ χ i, i < m → (prover τ χ i).degree < ((3 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb ((Fin m → F) × (Fin m → F)) (fun p =>
      SumcheckAccepts (prover p.1 (chalOf p.2)) (sopHonest (zcFactors svcs z p.1 T) (chalOf p.2))
        0 (∑ b, sop (zcFactors svcs z p.1 T) (cubePt b)) p.2)
      ≤ (m : ℝ) / Fintype.card F + (m : ℝ) * ((3 : ℝ) / Fintype.card F) := by
  have hrow : ∃ r ∈ svcs.rows, r.resid z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hbad (credible_cert_knowledge_soundness hchk ⟨hz0, hcon, hlk⟩)
  obtain ⟨r, hr, hne⟩ := hrow
  set D : (Fin m → Bool) → F := fun b => (rowAt svcs (cubeIdx m b)).resid z
  have hD : D ≠ 0 := by
    obtain ⟨b, hb⟩ := defect_witness svcs z hm hr hne
    exact fun h0 => hb (congrFun h0 b)
  set S : (Fin m → F) → F := fun τ => ∑ b, sop (zcFactors svcs z τ T) (cubePt b)
  have hS : ∀ τ, S τ = ∑ b, eqMle τ (cubePt b) * D b := fun τ =>
    Finset.sum_congr rfl fun b _ => sop_zc_cube svcs z τ hT b
  have hsplit : ∀ p : (Fin m → F) × (Fin m → F),
      SumcheckAccepts (prover p.1 (chalOf p.2)) (sopHonest (zcFactors svcs z p.1 T) (chalOf p.2))
        0 (S p.1) p.2 →
      S p.1 = 0 ∨ AdaptiveAcceptsFalse (prover p.1) (sopHonest (zcFactors svcs z p.1 T)) 0
        (S p.1) p.2 := by
    intro p hacc
    by_cases h0 : S p.1 = 0
    · exact Or.inl h0
    · exact Or.inr (acceptsFalse_iff_accepts.2 ⟨hacc, fun h => h0 h.symm⟩)
  refine (uniformProb_mono hsplit).trans ((uniformProb_or_le _ _).trans (add_le_add ?_ ?_))
  · -- zero-test slack, fibred over the sum-check challenges
    rw [← uniformProb_equiv (Equiv.prodComm (Fin m → F) (Fin m → F))]
    refine uniformProb_prod_le (by positivity) fun _ => ?_
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, hS]
    exact eqMle_zero_test hD
  · -- adaptive sum-check soundness at the degree-3 realizer, fibred over `τ`
    refine uniformProb_prod_le (by positivity) fun τ => ?_
    apply adaptive_sumcheck_soundness (v := m) (d := 3) (H := 0) (S := S τ) (prover := prover τ)
      (honest := sopHonest (zcFactors svcs z τ T)) (hpm τ) (sopHonest_prefixMeasurable _) (hdeg τ)
    · exact sopHonest_natDegree (zcFactors_length svcs z τ T)
    · exact sopHonest_boolean_sum (zcFactors_affine svcs z τ T)
end Composed

/-! ## §8. Teeth over `ZMod 7` (kernel-decided) -/
section Teeth
instance : LaneSemantics (ZMod 7) := ⟨fun _ _ => true⟩
/-- `x₀·x₁ = x₂`, `x₂·x₃ = x₄`, `x₀ = 3` (public), `x₂ + x₃ = x₅` with `x₅ = 0` zero-checked. -/
def tSpec : FrontSpec (ZMod 7) :=
  ⟨6, [.gate ⟨.mul, .wire 0, .wire 1, 2⟩, .gate ⟨.mul, .wire 2, .wire 3, 4⟩, .pin 0 3,
    .gate ⟨.add, .wire 2, .wire 3, 5⟩, .zero (.wire 5)]⟩
def tCompiled : SvcsInstance (ZMod 7) × CredibleLoweringCert (ZMod 7) := compile tSpec
theorem teeth_compiled_accepted : checkCredibleCert tSpec tCompiled.1 tCompiled.2 = true := by decide
def tBadFuse : Bool :=
  let a := gateRow ⟨.mul, .wire 0, .wire 1, 2⟩
  let b := gateRow ⟨.mul, .wire 2, .wire 3, 4⟩
  let onlyPair := { tSpec with items := tSpec.items.take 2 }
  checkCredibleCert onlyPair (fuseInst (lowerRef onlyPair) a b 3) ⟨[.fuse a b 3], []⟩
theorem teeth_degree_inflating_fusion_rejected : tBadFuse = false := by decide
/-- The instance with the public-input pin row dropped. -/
def tNoPin : SvcsInstance (ZMod 7) :=
  { tCompiled.1 with rows := tCompiled.1.rows.erase ⟨[], [(1, 1), (-3, 0)]⟩ }
theorem teeth_missing_pin_rejected : checkCredibleCert tSpec tNoPin tCompiled.2 = false := by decide
/-- Why the rejection is load-bearing: `tNoPin` is satisfied by a witness whose extraction breaks
the pin, so accepting it would falsify `credible_cert_knowledge_soundness`. -/
theorem teeth_missing_pin_would_be_unsound :
    ∃ z : ℕ → ZMod 7, tNoPin.Satisfied z ∧ ¬ tSpec.Holds (tCompiled.2.extractWitness z) :=
  ⟨fun j => if j = 0 then 1 else 0, by decide⟩
/-- Dead-column elimination that drops an ACTIVE wire (`x₄`, SVCS wire 5) is refused. -/
def tBadDce : Bool :=
  let keep := [0, 1, 2, 3, 4, 6]
  checkCredibleCert tSpec (renameInst keep.idxOf keep.length (lowerRef tSpec)) ⟨[.dce keep], []⟩
theorem teeth_unguarded_dce_rejected : tBadDce = false := by decide
end Teeth

/-! ## §9. BabyBear conformance bundles (emitted by `#eval`) -/
section Conformance
abbrev BB := BabyBear
instance : LaneSemantics BB := ⟨fun ℓ v => match ℓ with
  | .u8 => decide (v.val < 256)
  | .i8 => decide (v.val < 128 ∨ babyBearP - 128 ≤ v.val)
  | .i16 => decide (v.val < 32768 ∨ babyBearP - 32768 ≤ v.val)
  | .u32 => true⟩
def u8Table : List BB := (List.range 256).map fun n => (n : BB)
def i8Table : List BB := (List.range 256).map fun n => ((n : ℤ) - 128 : BB)
/-- Spec 1: two-limb u8 add-with-carry (EVM-style ADD gate rows, Emit gate records). -/
def evmSpec : FrontSpec BB :=
  let g := @DGate.mk BB
  let d : ConstraintDescriptor BB := ⟨4, 8, 27, [g .add (.wire 0) (.wire 2) 8, g .mul (.cnst 256) (.wire 6) 9,
    g .add (.wire 4) (.wire 9) 10, g .mul (.cnst (-1)) (.wire 10) 11,
    g .add (.wire 8) (.wire 11) 12,
    g .add (.wire 1) (.wire 3) 13, g .add (.wire 13) (.wire 6) 14,
    g .mul (.cnst 256) (.wire 7) 15, g .add (.wire 5) (.wire 15) 16,
    g .mul (.cnst (-1)) (.wire 16) 17, g .add (.wire 14) (.wire 17) 18,
    g .mul (.wire 6) (.wire 6) 19, g .mul (.cnst (-1)) (.wire 6) 20,
    g .add (.wire 19) (.wire 20) 21,
    g .mul (.wire 7) (.wire 7) 22, g .mul (.cnst (-1)) (.wire 7) 23,
    g .add (.wire 22) (.wire 23) 24], [12, 18, 21, 24].map .wire⟩
  let base := FrontSpec.ofDescriptor d
  { base with items := base.items ++ [.pin 0 200, .pin 1 17, .pin 2 100, .pin 3 3] ++
    [0, 1, 2, 3, 4, 5].map fun i => .lookup i u8Table }
def evmWitness : List BB :=
  [200, 17, 100, 3, 44, 21, 1, 0, 300, 256, 300, -300, 0, 20, 21, 0, 21, -21, 0,
    1, -1, 0, 0, 0, 0, 0, 0]
def mmA : List ℤ := (List.range 16).map fun i => ((i * 37 + 11) % 256 : ℤ) - 128
def mmB : List ℤ := (List.range 16).map fun i => ((i * 91 + 5) % 256 : ℤ) - 128
def mmC : List ℤ := (List.range 16).map fun ij =>
  ((List.range 4).map fun l => mmA.getD (ij / 4 * 4 + l) 0 * mmB.getD (l * 4 + ij % 4) 0).sum
/-- Spec 2: `EinSumcheck`-style i8×i8 4×4×4 contraction, inputs range-checked, one output public;
the contraction claim appears twice (two consumers), so `dedupClaims` has work. -/
def mmSpec : FrontSpec BB :=
  ⟨48, [.matmul 4 4 4 0 16 32, .matmul 4 4 4 0 16 32, .pin 32 (mmC.getD 0 0 : BB)] ++
    (List.range 32).map fun i => .lookup i i8Table⟩
def mmWitness : List BB := (mmA ++ mmB ++ mmC).map fun x => (x : BB)
/-- Byte DFA for `[0-9]+`: states 0 (start), 1 (digits, accepting), 2 (sink). -/
def dfaStep (s c : ℕ) : ℕ := if s = 2 then 2 else if 48 ≤ c ∧ c ≤ 57 then 1 else 2
def dfaTable : List BB := ((List.range 3).flatMap fun s => (List.range 256).map fun c =>
  ((s + 4 * c + 1024 * dfaStep s c : ℕ) : BB))
/-- Spec 3: DFA over the 4-byte input "2026": packed transitions `s + 4c + 1024 s'` looked up in
the transition table, bytes range-checked, start/accept states public. Wires: states 0..4,
bytes 5..8, packed 9..12, intermediates 13..24. -/
def dfaSpec : FrontSpec BB :=
  let g := fun (op : GateOp) (a b : DWire BB) (o : ℕ) => FrontItem.gate ⟨op, a, b, o⟩
  ⟨25, ((List.range 4).flatMap fun t =>
      [g .mul (.cnst 4) (.wire (5 + t)) (13 + 3 * t), g .add (.wire t) (.wire (13 + 3 * t)) (14 + 3 * t),
       g .mul (.cnst 1024) (.wire (t + 1)) (15 + 3 * t),
       g .add (.wire (14 + 3 * t)) (.wire (15 + 3 * t)) (9 + t),
       .lookup (9 + t) dfaTable, .lookup (5 + t) u8Table, .lookup t [0, 1, 2]]) ++
    [.pin 0 0, .pin 4 1]⟩
def dfaBytes : List ℕ := [50, 48, 50, 54]
def dfaStates : List ℕ := [0, 1, 1, 1, 1]
def dfaWitness : List BB :=
  (dfaStates ++ dfaBytes ++ (List.range 4).map (fun t => dfaStates.getD t 0 + 4 * dfaBytes.getD t 0
      + 1024 * dfaStates.getD (t + 1) 0) ++ (List.range 4).flatMap fun t =>
    [4 * dfaBytes.getD t 0, dfaStates.getD t 0 + 4 * dfaBytes.getD t 0,
      1024 * dfaStates.getD (t + 1) 0]).map fun n => (n : BB)
def jForm (f : LinForm BB) : String :=
  "[" ++ ",".intercalate (f.map fun p => s!"[{p.1.val},{p.2}]") ++ "]"
def jRow (r : Row BB) : String :=
  "{\"p\":[" ++ ",".intercalate (r.prods.map fun ab => s!"[{jForm ab.1},{jForm ab.2}]") ++
    s!"],\"c\":{jForm r.c}}"
def jNats (l : List ℕ) : String := "[" ++ ",".intercalate (l.map toString) ++ "]"
def bundleJson (name kind : String) (spec : FrontSpec BB) (w : List BB) : String × Bool :=
  let (s, cert) := compile spec
  let wf : ℕ → BB := fun i => w.getD i 0
  let values := (List.range s.nZ).map (cert.forwardWitness wf)
  let z := fun i => values.getD i 0
  let readback := (List.range spec.nWires).map (cert.extractWitness z)
  let s0 := lowerRef spec
  let ok := checkCredibleCert spec s cert && decide (spec.Holds wf) && decide (s.Satisfied z) &&
    decide (spec.Holds (fun i => readback.getD i 0)) && (readback == w)
  let steps := cert.steps.map fun st => match st with
    | .dce _ => "\"dce\"" | .fuse _ _ t => s!"\"fuse:{t}\"" | .dedupClaims => "\"dedup_claims\""
  let back := cert.steps.map fun st => match st with
    | .dce keep => s!"\{\"keep\":{jNats keep}}"
    | .fuse r _ t => s!"\{\"wire\":{t},\"form\":{jForm (scale (-(coefW t r.c)⁻¹) (dropW t r.c))}}"
    | .dedupClaims => "null"
  (s!"    \{\"name\":{(Lean.Json.str name).compress},\"spec_kind\":{(Lean.Json.str kind).compress},\"n_z\":{s.nZ},\"n_z_before\":{s0.nZ}," ++
    s!"\"rows_before\":{s0.rows.length},\"rows_after\":{s.rows.length}," ++
    s!"\"cost_before\":{s0.cost},\"cost_after\":{s.cost},\"lean_check\":{ok}," ++
    s!"\"extractor\":[{",".intercalate back}],\"extracted\":{jNats (readback.map ZMod.val)}," ++
    s!"\"steps\":[{",".intercalate steps}],\n     \"rows\":[" ++ ",".intercalate (s.rows.map jRow) ++
    "],\n     \"lookups\":[" ++ ",".intercalate (s.lookups.map fun l =>
      s!"\{\"f\":{jNats l.f},\"table\":{jNats (l.table.map ZMod.val)}}") ++
    "],\n     \"tags\":[" ++ ",".intercalate (cert.tags.map fun jl => s!"[{jl.1},\"{jl.2.name}\"]") ++
    s!"],\n     \"witness\":{jNats (values.map ZMod.val)}}", ok)
def emitSvcsConformance (path : System.FilePath) : IO Unit := do
  let (b1, ok1) := bundleJson "evm_u8_add_carry" "emit_gate_rows" evmSpec evmWitness
  let (b2, ok2) := bundleJson "einsum_i8_matmul_4x4x4" "einsumcheck_contraction" mmSpec mmWitness
  let (b3, ok3) := bundleJson "byte_dfa_digits_logup" "dfa_transition_lookup" dfaSpec dfaWitness
  let tPin := !checkCredibleCert tSpec tNoPin tCompiled.2
  let json := "{\n  \"schema\": \"minidregg.svcs_compiler_conformance.v1\"," ++
    " \"source\": \"Compiler/SvcsCredibleCompiler.lean\",\n" ++
    s!"  \"field\": \{\"p\": {babyBearP}, \"ext_degree\": 4, \"w\": 11},\n" ++
    s!"  \"lean_self_checks\": \{\"evm_ok\": {ok1}, \"einsum_ok\": {ok2}, \"dfa_ok\": {ok3}, " ++
    s!"\"degree_inflating_fusion_rejected\": {!tBadFuse}, \"missing_pin_rejected\": {tPin}, " ++
    s!"\"unguarded_dce_rejected\": {!tBadDce}},\n" ++
    "  \"bundles\": [\n" ++ ",\n".intercalate [b1, b2, b3] ++ "\n  ]\n}\n"
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path json

#eval emitSvcsConformance "prover/testdata/svcs_compiler_conformance.json"
end Conformance

/-! ## §10. Axiom audit -/
/-- info: 'Minidregg.Compiler.SvcsCredible.credible_cert_completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms credible_cert_completeness
/-- info: 'Minidregg.Compiler.SvcsCredible.credible_cert_knowledge_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms credible_cert_knowledge_soundness
/-- info: 'Minidregg.Compiler.SvcsCredible.credible_emit_knowledge_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms credible_emit_knowledge_soundness
/-- info: 'Minidregg.Compiler.SvcsCredible.credible_emit_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms credible_emit_accepts
/-- info: 'Minidregg.Compiler.SvcsCredible.svcs_rbr_soundness_composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms svcs_rbr_soundness_composed
/-- info: 'Minidregg.Compiler.SvcsCredible.tags_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tags_sound
/-- info: 'Minidregg.Compiler.SvcsCredible.teeth_compiled_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms teeth_compiled_accepted
/-- info: 'Minidregg.Compiler.SvcsCredible.teeth_degree_inflating_fusion_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms teeth_degree_inflating_fusion_rejected
/-- info: 'Minidregg.Compiler.SvcsCredible.teeth_missing_pin_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms teeth_missing_pin_rejected
/-- info: 'Minidregg.Compiler.SvcsCredible.teeth_missing_pin_would_be_unsound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms teeth_missing_pin_would_be_unsound
/-- info: 'Minidregg.Compiler.SvcsCredible.teeth_unguarded_dce_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms teeth_unguarded_dce_rejected
end Minidregg.Compiler.SvcsCredible
