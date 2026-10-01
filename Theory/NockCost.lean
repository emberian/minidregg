import Theory.Nock
import Theory.NockCost.Shape
import Theory.AssertAxioms

namespace Minidregg.Theory
namespace NockCost

open Noun Nock

/-! ## Shape operations, each mirroring the noun operation it over-approximates -/

/-- Head and tail shapes of a shape that holds a cell. -/
def split : Shape → Shape × Shape
  | .exact (.cell h t) => (.exact h, .exact t)
  | .cell a b => (a, b)
  | .list (n + 1) e => (e, .list n e)
  | .any => (.any, .any)
  | _ => (.bot, .bot)

def sAxisAux : Nat → Nat → Shape → Shape
  | 0, _, _ => .bot
  | k + 1, a, sh =>
    if a = 0 then .bot
    else if a = 1 then sh
    else
      let p := split (sAxisAux k (a / 2) sh)
      if a % 2 = 0 then p.1 else p.2

def sAxis (a : Nat) (sh : Shape) : Shape := sAxisAux a a sh

def sEditAux : Nat → Nat → Shape → Shape → Shape
  | 0, _, _, _ => .any
  | k + 1, a, vs, ts =>
    if a = 0 then .any
    else if a = 1 then vs
    else
      let p := split (sAxis (a / 2) ts)
      sEditAux k (a / 2) (if a % 2 = 0 then .cell vs p.2 else .cell p.1 vs) ts

def sEdit (a : Nat) (vs ts : Shape) : Shape := sEditAux a a vs ts

def asRange : Shape → Option (Nat × Nat)
  | .exact (.atom k) => some (k, k)
  | .range lo hi => some (lo, hi)
  | _ => none

def isAtomic : Shape → Bool
  | .exact (.atom _) => true
  | .range _ _ => true
  | .atom => true
  | _ => false

def asCell : Shape → Option (Shape × Shape)
  | .exact (.cell h t) => some (.exact h, .exact t)
  | .cell a b => some (a, b)
  | _ => none

/-- One structural step of `join`: interval hull, atom, or cellwise with `j`. -/
def joinStep (j : Shape → Shape → Shape) (a b : Shape) : Shape :=
  match asRange a, asRange b with
  | some (l₁, h₁), some (l₂, h₂) => .range (min l₁ l₂) (max h₁ h₂)
  | _, _ =>
    if isAtomic a && isAtomic b then .atom
    else
      match asCell a, asCell b with
      | some (h₁, t₁), some (h₂, t₂) => .cell (j h₁ h₂) (j t₁ t₂)
      | _, _ => .any

def Shape.isBot : Shape → Bool
  | .bot => true
  | _ => false

/-- An upper bound of two shapes; `k` bounds the structural depth it descends. -/
def join : Nat → Shape → Shape → Shape
  | 0, _, _ => .any
  | k + 1, a, b =>
    if a.isBot then b
    else if b.isBot then a
    else
      match a, b with
      | .exact x, .exact y => if x = y then .exact x else joinStep (join k) (.exact x) (.exact y)
      | a, b => joinStep (join k) a b

/-- `%5` decided by intervals and cell/atom kinds. -/
def eqDecideS (a b : Shape) : Option Bool :=
  match asRange a, asRange b with
  | some (l₁, h₁), some (l₂, h₂) =>
    if h₁ < l₂ ∨ h₂ < l₁ then some false
    else if l₁ = h₁ ∧ l₂ = h₂ ∧ l₁ = l₂ then some true
    else none
  | _, _ =>
    if (isAtomic a && (asCell b).isSome) || ((asCell a).isSome && isAtomic b) then some false
    else none

/-- `%5` decided on shapes, when the shapes decide it. -/
def eqDecide : Shape → Shape → Option Bool
  | .exact x, .exact y => some (decide (x = y))
  | a, b => eqDecideS a b

def tisShape (a b : Shape) : Shape :=
  match eqDecide a b with
  | some c => .exact (loob c)
  | none => .range 0 1

def wutShape : Shape → Shape
  | .exact n => .exact (loob n.isCell)
  | .cell _ _ => .exact (loob true)
  | sh => if isAtomic sh then .exact (loob false) else .range 0 1

def lusShape : Shape → Shape
  | .exact (.atom k) => .exact (.atom (k + 1))
  | .range lo hi => .range (lo + 1) (hi + 1)
  | _ => .atom

/-- May an atom `k` have this shape? (over-approximate) -/
def mayBe (k : Nat) : Shape → Bool
  | .exact n => decide (n = .atom k)
  | .range lo hi => decide (lo ≤ k ∧ k ≤ hi)
  | .atom => true
  | .cell _ _ => false
  | .list _ _ => decide (k = 0)
  | .any => true
  | .bot => false

/-- What `w ≠ k` adds to a shape of `w`. -/
def neShape (k : Noun) : Shape → Shape
  | .range lo hi =>
    match k with
    | .atom m => if m = lo then .range (lo + 1) hi else if m = hi then .range lo (hi - 1) else .range lo hi
    | .cell _ _ => .range lo hi
  | .list (n + 1) e =>
    match k with
    | .atom 0 => .cell e (.list n e)
    | _ => .list (n + 1) e
  | sh => sh

/-- A `%6` test that compares a subject axis with something: `[5 [0 ax] w]` or `[5 w [0 ax]]`. -/
def testAxis : Noun → Option (Nat × Noun)
  | .cell (.atom 5) (.cell (.cell (.atom 0) (.atom ax)) w) => some (ax, w)
  | .cell (.atom 5) (.cell w (.cell (.atom 0) (.atom ax))) => some (ax, w)
  | _ => none

/-- Depth to which `join` descends. -/
def joinDepth : Nat := 64

/-- The subjects the two arms of `[6 x y z]` see: when `x` is `[5 [0 ax] w]` (either order) and
`w`'s product is known to be `k`, the yes arm knows `/[ax] = k` and the no arm `/[ax] ≠ k`. -/
def sixSubjects (ac : Noun → Option (Nat × Shape)) (sh : Shape) (x : Noun) : Shape × Shape :=
  match testAxis x with
  | some (ax, w) =>
    match ac w with
    | some (_, .exact k) => (sEdit ax (.exact k) sh, sEdit ax (neShape k (sAxis ax sh)) sh)
    | _ => (sh, sh)
  | none => (sh, sh)

/-- The product shape of `%6` from the arms that can be taken. -/
def sixOut (m₀ m₁ : Bool) (oy oz : Shape) : Shape :=
  if m₀ then (if m₁ then join joinDepth oy oz else oy) else if m₁ then oz else .bot

/-- A summary oracle (NC-2): for some (subject shape, formula) pairs, a step bound and product
shape proved once elsewhere (`Theory.NockCost.Summaries`), so the interpreter need not unroll the
loop the formula is. `none` = no summary: interpret the formula rule by rule. -/
abbrev Oracle := Shape → Noun → Option (Nat × Shape)

/-- No summaries: every loop is unrolled (NC-1's `cost`). -/
def noSummaries : Oracle := fun _ _ => none

/-- The abstract interpreter: an upper bound on the steps `exec` takes on any subject of shape
`sh`, and the shape of the product. `none` = outside the fragment (or the abstract fuel `D` ran
out). The oracle `O` is asked first at every node; where it answers, its summary is the price.
Otherwise: `%2` and `%9` need a formula whose shape is `exact`; every other rule is first-order. A
`%6` whose test the shapes decide costs one arm; otherwise it costs the dearer arm. -/
def acostWith (O : Oracle) : Nat → Shape → Noun → Option (Nat × Shape)
  | 0, _, _ => none
  | D + 1, sh, f =>
    match O sh f with
    | some r => some r
    | none =>
    match parse f with
    | none => some (1, .bot)
    | some (.cons x y z) =>
      (acostWith O D sh (.cell x y)).bind fun p₁ =>
      (acostWith O D sh z).bind fun p₂ =>
      some (1 + (p₁.1 + p₂.1), .cell p₁.2 p₂.2)
    | some (.slot a) => some (1, sAxis a sh)
    | some (.quote x) => some (1, .exact x)
    | some (.eval x y) =>
      (acostWith O D sh x).bind fun p₁ =>
      (acostWith O D sh y).bind fun p₂ =>
      match p₂.2 with
      | .exact g => (acostWith O D p₁.2 g).bind fun p₃ => some (1 + (p₁.1 + (p₂.1 + p₃.1)), p₃.2)
      | _ => none
    | some (.wut x) => (acostWith O D sh x).bind fun p₁ => some (1 + p₁.1, wutShape p₁.2)
    | some (.lus x) => (acostWith O D sh x).bind fun p₁ => some (1 + p₁.1, lusShape p₁.2)
    | some (.tis x y) =>
      (acostWith O D sh x).bind fun p₁ =>
      (acostWith O D sh y).bind fun p₂ =>
      some (1 + (p₁.1 + p₂.1), tisShape p₁.2 p₂.2)
    | some (.six x y z) =>
      (acostWith O D sh x).bind fun p₁ =>
      (if mayBe 0 p₁.2 then acostWith O D (sixSubjects (acostWith O D sh) sh x).1 y else some (0, .bot)).bind
        fun py =>
      (if mayBe 1 p₁.2 then acostWith O D (sixSubjects (acostWith O D sh) sh x).2 z else some (0, .bot)).bind
        fun pz =>
      some (1 + (p₁.1 + max py.1 pz.1), sixOut (mayBe 0 p₁.2) (mayBe 1 p₁.2) py.2 pz.2)
    | some (.seven x y) =>
      (acostWith O D sh x).bind fun p₁ =>
      (acostWith O D p₁.2 y).bind fun p₂ =>
      some (1 + (p₁.1 + p₂.1), p₂.2)
    | some (.eight x y) =>
      (acostWith O D sh x).bind fun p₁ =>
      (acostWith O D (.cell p₁.2 sh) y).bind fun p₂ =>
      some (1 + (p₁.1 + p₂.1), p₂.2)
    | some (.nine a c) =>
      (acostWith O D sh c).bind fun p₁ =>
      match sAxis a p₁.2 with
      | .exact g => (acostWith O D p₁.2 g).bind fun p₂ => some (1 + (p₁.1 + p₂.1), p₂.2)
      | _ => none
    | some (.ten a c z) =>
      (acostWith O D sh z).bind fun p₁ =>
      (acostWith O D sh c).bind fun p₂ =>
      some (1 + (p₁.1 + p₂.1), sEdit a p₂.2 p₁.2)
    | some (.hintS _ z) => (acostWith O D sh z).bind fun p₁ => some (1 + p₁.1, p₁.2)
    | some (.hintD _ c z) =>
      (acostWith O D sh c).bind fun p₁ =>
      (acostWith O D sh z).bind fun p₂ =>
      some (1 + (p₁.1 + p₂.1), p₂.2)

/-- NC-1's interpreter: every loop unrolled. -/
def acost : Nat → Shape → Noun → Option (Nat × Shape) := acostWith noSummaries

/-- Abstract fuel: the nesting depth the abstract interpreter may unroll. -/
def costFuel : Nat := 1000000

/-- The step bound of `f` on any subject of shape `sh`; `none` = outside the fragment. -/
def cost (sh : Shape) (f : Noun) : Option Nat := (acost costFuel sh f).map (·.1)


/-! ## Axis and edit, restated -/

theorem axisAux_fuel : ∀ (k k' a : Nat) (n : Noun), a ≤ k → a ≤ k' →
    axisAux k a n = axisAux k' a n
  | 0, k', a, n, h, _ => by
    obtain rfl : a = 0 := by omega
    cases k' <;> simp [axisAux]
  | k + 1, 0, a, n, _, h => by
    obtain rfl : a = 0 := by omega
    simp [axisAux]
  | k + 1, k' + 1, a, n, h, h' => by
    simp only [axisAux]
    by_cases h0 : a = 0
    · simp [h0]
    by_cases h1 : a = 1
    · simp [h1]
    simp only [h0, h1, if_false]
    rw [axisAux_fuel k k' (a / 2) n (by omega) (by omega)]

theorem axis_step {a : Nat} (n : Noun) (h2 : 2 ≤ a) :
    axis a n = match axis (a / 2) n with
      | some (.cell h t) => some (if a % 2 = 0 then h else t)
      | _ => none := by
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  unfold axis
  simp only [axisAux, show m + 1 ≠ 0 by omega, show m + 1 ≠ 1 by omega, if_false]
  rw [axisAux_fuel m ((m + 1) / 2) ((m + 1) / 2) n (by omega) le_rfl]
  rfl

theorem editAux_self : ∀ (k a : Nat) (v t : Noun), a ≤ k → axis a t = some v →
    editAux k a v t = some t
  | 0, a, v, t, h, hx => by
    obtain rfl : a = 0 := by omega
    simp [axis_zero] at hx
  | k + 1, a, v, t, h, hx => by
    simp only [editAux]
    by_cases h0 : a = 0
    · subst h0; simp [axis_zero] at hx
    by_cases h1 : a = 1
    · subst h1; rw [axis_one] at hx; cases hx; simp
    simp only [h0, h1, if_false]
    rw [axis_step t (by omega)] at hx
    cases hp : axis (a / 2) t with
    | none => rw [hp] at hx; simp at hx
    | some c =>
      rw [hp] at hx
      cases c with
      | atom _ => simp at hx
      | cell hh tt =>
        simp only [Option.some.injEq] at hx
        simp only
        apply editAux_self k (a / 2) _ t (by omega)
        rw [hp]
        split_ifs at hx ⊢ <;> subst hx <;> rfl

/-- Writing back what an axis holds changes nothing. -/
theorem edit_self {a : Nat} {v t : Noun} (hx : axis a t = some v) : edit a v t = some t :=
  editAux_self a a v t le_rfl hx

/-! ## Shape membership -/

@[simp] theorem fits_exact {v n : Noun} : fits v (.exact n) = true ↔ v = n := by
  simp [fits]

@[simp] theorem fits_any (v : Noun) : fits v .any = true := by
  cases v <;> simp [fits]

@[simp] theorem fits_bot (v : Noun) : fits v .bot = false := by
  cases v <;> simp [fits]

theorem split_sound {h t : Noun} {sh : Shape} (hf : fits (.cell h t) sh = true) :
    fits h (split sh).1 = true ∧ fits t (split sh).2 = true := by
  cases sh with
  | exact n => rw [fits_exact] at hf; subst hf; simp [split]
  | range lo hi => simp [fits] at hf
  | atom => simp [fits] at hf
  | cell a b => simpa [fits, split] using hf
  | list n e =>
    cases n with
    | zero => simp [fits] at hf
    | succ n => simpa [fits, split] using hf
  | any => simp [split]
  | bot => simp at hf

theorem sAxisAux_sound : ∀ (k a : Nat) (n v : Noun) (sh : Shape), fits n sh = true →
    axisAux k a n = some v → fits v (sAxisAux k a sh) = true
  | 0, _, _, _, _, _, h => by simp [axisAux] at h
  | k + 1, a, n, v, sh, hn, h => by
    simp only [axisAux] at h
    simp only [sAxisAux]
    by_cases h0 : a = 0
    · simp [h0] at h
    by_cases h1 : a = 1
    · simp only [h1, one_ne_zero, if_true, if_false, Option.some.injEq] at h ⊢; subst h; exact hn
    simp only [h0, h1, if_false] at h ⊢
    cases hp : axisAux k (a / 2) n with
    | none => rw [hp] at h; simp at h
    | some c =>
      rw [hp] at h
      cases c with
      | atom _ => simp at h
      | cell hh tt =>
        simp only [Option.some.injEq] at h
        have hs := split_sound (sAxisAux_sound k (a / 2) n _ sh hn hp)
        split_ifs at h ⊢ <;> subst h
        · exact hs.1
        · exact hs.2

theorem sAxis_sound {a : Nat} {n v : Noun} {sh : Shape} (hn : fits n sh = true)
    (h : axis a n = some v) : fits v (sAxis a sh) = true :=
  sAxisAux_sound a a n v sh hn h

theorem sEditAux_sound : ∀ (k a : Nat) (v t r : Noun) (vs ts : Shape), fits v vs = true →
    fits t ts = true → editAux k a v t = some r → fits r (sEditAux k a vs ts) = true
  | 0, _, _, _, _, _, _, _, _, h => by simp [editAux] at h
  | k + 1, a, v, t, r, vs, ts, hv, ht, h => by
    simp only [editAux] at h
    simp only [sEditAux]
    by_cases h0 : a = 0
    · simp [h0] at h
    by_cases h1 : a = 1
    · simp only [h1, one_ne_zero, if_true, if_false, Option.some.injEq] at h ⊢; subst h; exact hv
    simp only [h0, h1, if_false] at h ⊢
    cases hp : axis (a / 2) t with
    | none => rw [hp] at h; simp at h
    | some c =>
      rw [hp] at h
      cases c with
      | atom _ => simp at h
      | cell hh tt =>
        simp only at h
        have hs := split_sound (sAxis_sound ht hp)
        refine sEditAux_sound k (a / 2) _ t r _ ts ?_ ht h
        split_ifs <;> simp [fits, hv, hs.1, hs.2]

theorem sEdit_sound {a : Nat} {v t r : Noun} {vs ts : Shape} (hv : fits v vs = true)
    (ht : fits t ts = true) (h : edit a v t = some r) : fits r (sEdit a vs ts) = true :=
  sEditAux_sound a a v t r vs ts hv ht h

theorem asRange_sound {x : Noun} {a : Shape} {l h : Nat} (hx : fits x a = true)
    (hr : asRange a = some (l, h)) : ∃ k, x = .atom k ∧ l ≤ k ∧ k ≤ h := by
  cases a with
  | exact n =>
    rw [fits_exact] at hx; subst hx
    cases x with
    | atom k => simp only [asRange, Option.some.injEq, Prod.mk.injEq] at hr; exact ⟨k, rfl, by omega⟩
    | cell _ _ => simp [asRange] at hr
  | range lo hi =>
    simp only [asRange, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    cases x with
    | atom k => simp [fits] at hx; exact ⟨k, rfl, hx⟩
    | cell _ _ => simp [fits] at hx
  | _ => simp [asRange] at hr

theorem isAtomic_sound {x : Noun} {a : Shape} (hx : fits x a = true) (ha : isAtomic a = true) :
    ∃ k, x = .atom k := by
  cases a with
  | exact n =>
    rw [fits_exact] at hx; subst hx
    cases x with
    | atom k => exact ⟨k, rfl⟩
    | cell _ _ => simp [isAtomic] at ha
  | range lo hi => cases x with
    | atom k => exact ⟨k, rfl⟩
    | cell _ _ => simp [fits] at hx
  | atom => cases x with
    | atom k => exact ⟨k, rfl⟩
    | cell _ _ => simp [fits] at hx
  | _ => simp [isAtomic] at ha

theorem asCell_sound {x : Noun} {a p q : Shape} (hx : fits x a = true)
    (ha : asCell a = some (p, q)) : ∃ h t, x = .cell h t ∧ fits h p = true ∧ fits t q = true := by
  cases a with
  | exact n =>
    rw [fits_exact] at hx; subst hx
    cases x with
    | atom k => simp [asCell] at ha
    | cell h t =>
      simp only [asCell, Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      exact ⟨h, t, rfl, by simp, by simp⟩
  | cell a b =>
    simp only [asCell, Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    cases x with
    | atom k => simp [fits] at hx
    | cell h t => simp only [fits, Bool.and_eq_true] at hx; exact ⟨h, t, rfl, hx.1, hx.2⟩
  | _ => simp [asCell] at ha

theorem joinStep_sound {j : Shape → Shape → Shape}
    (hj : ∀ a b v, (fits v a = true ∨ fits v b = true) → fits v (j a b) = true)
    {a b : Shape} {v : Noun} (h : fits v a = true ∨ fits v b = true) :
    fits v (joinStep j a b) = true := by
  unfold joinStep
  split
  · rename_i l₁ h₁ l₂ h₂ ha hb
    rcases h with h | h
    · obtain ⟨k, rfl, hk⟩ := asRange_sound h ha
      simp [fits]; omega
    · obtain ⟨k, rfl, hk⟩ := asRange_sound h hb
      simp [fits]; omega
  · split_ifs with hat
    · simp only [Bool.and_eq_true] at hat
      rcases h with h | h
      · obtain ⟨k, rfl⟩ := isAtomic_sound h hat.1; simp [fits]
      · obtain ⟨k, rfl⟩ := isAtomic_sound h hat.2; simp [fits]
    · split
      · rename_i h₁ t₁ h₂ t₂ ha hb
        rcases h with h | h
        · obtain ⟨x, y, rfl, hx, hy⟩ := asCell_sound h ha
          simp [fits, hj _ _ _ (Or.inl hx), hj _ _ _ (Or.inl hy)]
        · obtain ⟨x, y, rfl, hx, hy⟩ := asCell_sound h hb
          simp [fits, hj _ _ _ (Or.inr hx), hj _ _ _ (Or.inr hy)]
      · simp

theorem isBot_sound {v : Noun} {a : Shape} (ha : a.isBot = true) : fits v a = false := by
  cases a <;> simp_all [Shape.isBot]

theorem join_sound : ∀ (k : Nat) (a b : Shape) (v : Noun),
    (fits v a = true ∨ fits v b = true) → fits v (join k a b) = true
  | 0, _, _, _, _ => by simp [join]
  | k + 1, a, b, v, h => by
    simp only [join]
    split_ifs with ha hb
    · simpa [isBot_sound ha] using h
    · simpa [isBot_sound hb] using h
    · split
      · split_ifs with hxy
        · subst hxy; simpa using h
        · exact joinStep_sound (join_sound k) h
      · exact joinStep_sound (join_sound k) h

theorem eqDecideS_sound {x y : Noun} {a b : Shape} {c : Bool} (hx : fits x a = true)
    (hy : fits y b = true) (h : eqDecideS a b = some c) : decide (x = y) = c := by
  unfold eqDecideS at h
  split at h
  · rename_i l₁ h₁ l₂ h₂ ha hb
    obtain ⟨k₁, rfl, hk₁⟩ := asRange_sound hx ha
    obtain ⟨k₂, rfl, hk₂⟩ := asRange_sound hy hb
    split_ifs at h with hd hs
    · cases h; simp; omega
    · cases h; simp; omega
  · split_ifs at h with hc
    cases h
    simp only [Bool.or_eq_true, Bool.and_eq_true, Option.isSome_iff_exists] at hc
    rcases hc with ⟨ha, ⟨⟨p, q⟩, hb⟩⟩ | ⟨⟨⟨p, q⟩, ha⟩, hb⟩
    · obtain ⟨k, rfl⟩ := isAtomic_sound hx ha
      obtain ⟨h', t', rfl, -⟩ := asCell_sound hy hb
      simp
    · obtain ⟨h', t', rfl, -⟩ := asCell_sound hx ha
      obtain ⟨k, rfl⟩ := isAtomic_sound hy hb
      simp

theorem eqDecide_sound {x y : Noun} {a b : Shape} {c : Bool} (hx : fits x a = true)
    (hy : fits y b = true) (h : eqDecide a b = some c) : decide (x = y) = c := by
  unfold eqDecide at h
  split at h
  · rw [fits_exact] at hx hy; subst hx; subst hy; simpa using h
  · exact eqDecideS_sound hx hy h

theorem loob_fits_bool (c : Bool) : fits (loob c) (.range 0 1) = true := by
  cases c <;> simp [loob, fits]

theorem tisShape_sound {x y : Noun} {a b : Shape} (hx : fits x a = true) (hy : fits y b = true) :
    fits (loob (decide (x = y))) (tisShape a b) = true := by
  unfold tisShape
  split
  · rename_i c hc
    rw [eqDecide_sound hx hy hc]; simp
  · exact loob_fits_bool _

theorem wutShape_sound {v : Noun} {sh : Shape} (hv : fits v sh = true) :
    fits (loob v.isCell) (wutShape sh) = true := by
  cases sh with
  | exact n => rw [fits_exact] at hv; subst hv; simp [wutShape]
  | cell a b =>
    cases v with
    | atom _ => simp [fits] at hv
    | cell _ _ => simp [wutShape, isCell]
  | range lo hi =>
    obtain ⟨k, rfl⟩ := isAtomic_sound hv rfl
    simp [wutShape, isAtomic, isCell]
  | atom =>
    obtain ⟨k, rfl⟩ := isAtomic_sound hv rfl
    simp [wutShape, isAtomic, isCell]
  | list n e => simp only [wutShape, isAtomic]; exact loob_fits_bool _
  | any => simp only [wutShape, isAtomic]; exact loob_fits_bool _
  | bot => simp at hv

theorem lusShape_sound {n : Nat} {sh : Shape} (hv : fits (.atom n) sh = true) :
    fits (.atom (n + 1)) (lusShape sh) = true := by
  cases sh with
  | exact m =>
    rw [fits_exact] at hv; subst hv; simp [lusShape]
  | range lo hi => simp [fits, lusShape] at hv ⊢; omega
  | _ => simp [lusShape, fits]

theorem mayBe_sound {k : Nat} {sh : Shape} (h : fits (.atom k) sh = true) : mayBe k sh = true := by
  cases sh with
  | exact n => rw [fits_exact] at h; subst h; simp [mayBe]
  | range lo hi => simpa [fits, mayBe] using h
  | list n e => simpa [fits, mayBe] using h
  | cell a b => simp [fits] at h
  | bot => simp at h
  | _ => simp [mayBe]

theorem neShape_sound {w k : Noun} {s : Shape} (hw : fits w s = true) (hne : w ≠ k) :
    fits w (neShape k s) = true := by
  cases s with
  | range lo hi =>
    cases w with
    | cell _ _ => simp [fits] at hw
    | atom j =>
      simp only [fits, decide_eq_true_eq] at hw
      cases k with
      | cell _ _ => simpa [neShape, fits] using hw
      | atom m =>
        have hjm : j ≠ m := fun e => hne (by rw [e])
        simp only [neShape]
        split_ifs <;> simp [fits] <;> omega
  | list n e =>
    cases n with
    | zero => simpa [neShape] using hw
    | succ n =>
      cases w with
      | atom j =>
        simp [fits] at hw; subst hw
        cases k with
        | atom m =>
          cases m with
          | zero => exact absurd rfl hne
          | succ m => simp [neShape, fits]
        | cell _ _ => simp [neShape, fits]
      | cell h t =>
        cases k with
        | atom m =>
          cases m with
          | zero => simpa [neShape, fits] using hw
          | succ m => simpa [neShape] using hw
        | cell _ _ => simpa [neShape] using hw
  | _ => exact hw

theorem testAxis_some {x w : Noun} {ax : Nat} (h : testAxis x = some (ax, w)) :
    x = .cell (.atom 5) (.cell (.cell (.atom 0) (.atom ax)) w) ∨
      x = .cell (.atom 5) (.cell w (.cell (.atom 0) (.atom ax))) := by
  unfold testAxis at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  · obtain ⟨rfl, rfl⟩ := h; exact Or.inl rfl
  · obtain ⟨rfl, rfl⟩ := h; exact Or.inr rfl

/-! ## Soundness of the abstract interpreter -/

/-- A run result within `B` steps of a budget `b`, with a product of shape `o`. -/
def Res.within : Res → Nat → Nat → Shape → Prop
  | .ok v r, b, B, o => fits v o = true ∧ b ≤ r + B
  | .crash r, b, B, _ => b ≤ r + B
  | .exhausted, _, _, _ => True

theorem Res.within.bind {x : Res} {k : Noun → Nat → Res} {b B₁ B₂ B : Nat} {o₁ o₂ : Shape}
    (hx : Res.within x b B₁ o₁)
    (hk : ∀ v r, x = .ok v r → fits v o₁ = true → Res.within (k v r) r B₂ o₂)
    (hB : B₁ + B₂ ≤ B) : Res.within (x.bind k) b B o₂ := by
  cases x with
  | ok v r =>
    obtain ⟨hv, hr⟩ := hx
    have hk' := hk v r rfl hv
    simp only [Res.bind]
    cases hkv : k v r with
    | ok v' r' => rw [hkv] at hk'; exact ⟨hk'.1, by have := hk'.2; omega⟩
    | crash r' => rw [hkv] at hk'; simp only [Res.within] at hk' ⊢; omega
    | exhausted => trivial
  | crash r => simp only [Res.bind, Res.within] at hx ⊢; omega
  | exhausted => trivial

theorem Res.within.bind_ne {x : Res} {k : Noun → Nat → Res} {b B₁ B₂ : Nat} {o₁ : Shape}
    (hx : Res.within x b B₁ o₁) (hne : x ≠ .exhausted)
    (hk : ∀ v r, x = .ok v r → fits v o₁ = true → B₂ ≤ r → k v r ≠ .exhausted)
    (hB : B₁ + B₂ ≤ b) : x.bind k ≠ .exhausted := by
  cases x with
  | ok v r => exact hk v r rfl hx.1 (by have := hx.2; omega)
  | crash r => simp [Res.bind]
  | exhausted => exact absurd rfl hne

theorem Res.within.mono {x : Res} {b B B' : Nat} {o o' : Shape} (h : Res.within x b B o)
    (hB : B ≤ B') (ho : ∀ v, fits v o = true → fits v o' = true) : Res.within x b B' o' := by
  cases x with
  | ok v r => exact ⟨ho _ h.1, by have := h.2; omega⟩
  | crash r => simp only [Res.within] at h ⊢; omega
  | exhausted => trivial

theorem Res.within.succ {x : Res} {b B : Nat} {o : Shape} (h : Res.within x b B o) :
    Res.within x (b + 1) (1 + B) o := by
  cases x with
  | ok v r => exact ⟨h.1, by have := h.2; omega⟩
  | crash r => simp only [Res.within] at h ⊢; omega
  | exhausted => trivial

theorem Res.within.ok {v : Noun} {r b B : Nat} {o : Shape} (hv : fits v o = true) (hr : b ≤ r + B) :
    Res.within (.ok v r) b B o := ⟨hv, hr⟩

/-- `B` bounds every run of `f` on `s` and `o` shapes its product; with at least `B` budget and
depth, the run is never exhausted. -/
def Sound (B : Nat) (o : Shape) (s f : Noun) : Prop :=
  ∀ d b, Res.within (exec d b s f) b B o ∧ (B ≤ d → B ≤ b → exec d b s f ≠ .exhausted)

/-- An oracle is sound when every summary it gives is a price: `Sound` on every subject of the
shape it was asked about. -/
def OracleSound (O : Oracle) : Prop :=
  ∀ sh f B o, O sh f = some (B, o) → ∀ s, fits s sh = true → Sound B o s f

theorem noSummaries_sound : OracleSound noSummaries := fun _ _ _ _ h => by simp [noSummaries] at h

theorem Sound.of_succ {B : Nat} {o : Shape} {s f : Noun} (hB : 1 ≤ B)
    (h : ∀ d b, Res.within (exec (d + 1) (b + 1) s f) (b + 1) B o ∧
      (B ≤ d + 1 → B ≤ b + 1 → exec (d + 1) (b + 1) s f ≠ .exhausted)) : Sound B o s f := by
  intro d b
  cases d with
  | zero => simp only [exec]; exact ⟨trivial, fun h _ => absurd h (by omega)⟩
  | succ d =>
    cases b with
    | zero => simp only [exec]; exact ⟨trivial, fun _ h => absurd h (by omega)⟩
    | succ b => exact h d b

/-- What a refined `%6` arm may assume about its subject. -/
theorem sixSubjects_sound {ac : Noun → Option (Nat × Shape)} {sh : Shape} {x s : Noun}
    (hac : ∀ w B k, ac w = some (B, .exact k) → Sound B (.exact k) s w)
    (hs : fits s sh = true) {d b : Nat} {v : Noun} {r : Nat} (hx : exec d b s x = .ok v r) :
    (v = .atom 0 → fits s (sixSubjects ac sh x).1 = true) ∧
      (v = .atom 1 → fits s (sixSubjects ac sh x).2 = true) := by
  unfold sixSubjects
  split
  · rename_i ax w ht
    split
    · rename_i Bw k hw
      have hW := hac w Bw k hw
      -- the test's two operands: `/[ax]` of the subject and `w`'s product `k`
      have key : ∃ u, axis ax s = some u ∧ v = loob (decide (u = k)) := by
        rcases testAxis_some ht with rfl | rfl
        · rcases d with _ | d; · simp [exec] at hx
          rcases b with _ | b; · simp [exec] at hx
          simp only [exec, parse] at hx
          rcases d with _ | d; · simp [exec, Res.bind] at hx
          rcases b with _ | b; · simp [exec, Res.bind] at hx
          simp only [exec, parse] at hx
          cases hu : axis ax s with
          | none => simp [hu, Res.bind] at hx
          | some u =>
            simp only [hu, Res.bind] at hx
            cases hwr : exec (d + 1) b s w with
            | ok w' r' =>
              rw [hwr] at hx
              simp only [Res.ok.injEq] at hx
              have := ((hW (d + 1) b).1)
              rw [hwr] at this
              have hw' : w' = k := fits_exact.mp this.1
              exact ⟨u, rfl, by rw [← hw']; exact hx.1.symm⟩
            | crash r' => rw [hwr] at hx; simp at hx
            | exhausted => rw [hwr] at hx; simp at hx
        · rcases d with _ | d; · simp [exec] at hx
          rcases b with _ | b; · simp [exec] at hx
          simp only [exec, parse] at hx
          cases hwr : exec d b s w with
          | ok w' r' =>
            rw [hwr] at hx
            simp only [Res.bind] at hx
            have := ((hW d b).1)
            rw [hwr] at this
            have hw' : w' = k := fits_exact.mp this.1
            subst hw'
            rcases d with _ | d; · simp [exec] at hx
            rcases r' with _ | r'; · simp [exec] at hx
            simp only [exec, parse] at hx
            cases hu : axis ax s with
            | none => simp [hu] at hx
            | some u =>
              simp only [hu, Res.ok.injEq] at hx
              refine ⟨u, rfl, ?_⟩
              rw [← hx.1]; congr 1; exact decide_eq_decide.mpr ⟨Eq.symm, Eq.symm⟩
          | crash r' => rw [hwr] at hx; simp [Res.bind] at hx
          | exhausted => rw [hwr] at hx; simp [Res.bind] at hx
      obtain ⟨u, hu, rfl⟩ := key
      have hsame : edit ax u s = some s := edit_self hu
      constructor
      · intro h0
        have : u = k := by
          by_contra hne; simp [loob, hne] at h0
        subst this
        exact sEdit_sound (by simp) hs hsame
      · intro h1
        have hne : u ≠ k := by
          intro e; simp [loob, e] at h1
        exact sEdit_sound (neShape_sound (sAxis_sound hs hu) hne) hs hsame
    · exact ⟨fun _ => hs, fun _ => hs⟩
  · exact ⟨fun _ => hs, fun _ => hs⟩

/-- **Soundness of the abstract interpreter.** If `acost` answers `(B, o)` on `f` and `sh`, then on
every subject of shape `sh`: every run of `f` (any depth, any budget) that ends ends within `B`
steps with a product of shape `o`, and a run given at least `B` budget and depth never exhausts. -/
theorem acostWith_sound {O : Oracle} (hO : OracleSound O) : ∀ (D : Nat) (sh : Shape) (f : Noun)
    (B : Nat) (o : Shape), acostWith O D sh f = some (B, o) → ∀ s, fits s sh = true → Sound B o s f
  | 0, _, _, _, _, h, _, _ => by simp [acostWith] at h
  | D + 1, sh, f, B, o, h, s, hs => by
    have IH := acostWith_sound hO D
    simp only [acostWith] at h
    cases hO' : O sh f
    case some r =>
      rw [hO'] at h
      simp only [Option.some.injEq] at h
      subst h
      exact hO _ _ _ _ hO' s hs
    rw [hO'] at h
    simp only at h
    cases hp : parse f with
    | none =>
      rw [hp] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine Sound.of_succ le_rfl fun d b => ?_
      simp only [exec, hp]
      exact ⟨by simp [Res.within], fun _ _ => by simp⟩
    | some form =>
      rw [hp] at h
      cases form with
      | cons x y z =>
        obtain ⟨⟨b₁, o₁⟩, h₁, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨b₂, o₂⟩, h₂, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have S₁ := IH sh _ _ _ h₁ s hs
        have S₂ := IH sh _ _ _ h₂ s hs
        refine Sound.of_succ (by omega) fun d b => ?_
        simp only [exec, hp]
        refine ⟨Res.within.succ ((S₁ d b).1.bind (fun hv r _ hhv =>
          (S₂ d r).1.bind (B₂ := 0) (fun tv r' _ htv => ⟨by simp [fits, hhv, htv], by omega⟩)
            (by omega)) le_rfl),
          fun hd hb => ?_⟩
        exact (S₁ d b).1.bind_ne ((S₁ d b).2 (by omega) (by omega)) (B₂ := b₂)
          (fun hv r _ _ hr => (S₂ d r).1.bind_ne ((S₂ d r).2 (by omega) hr) (B₂ := 0)
            (fun _ _ _ _ _ => by simp) (by omega)) (by omega)
      | slot a =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine Sound.of_succ le_rfl fun d b => ?_
        simp only [exec, hp]
        constructor
        · cases hx : axis a s with
          | some v => exact ⟨sAxis_sound hs hx, by omega⟩
          | none => simp only [Res.within]; omega
        · intro _ _; cases axis a s <;> simp
      | quote x =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine Sound.of_succ le_rfl fun d b => ?_
        simp only [exec, hp]
        exact ⟨⟨by simp, by omega⟩, fun _ _ => by simp⟩
      | eval x y =>
        obtain ⟨⟨b₁, o₁⟩, h₁, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨b₂, o₂⟩, h₂, h⟩ := Option.bind_eq_some_iff.mp h
        simp only at h
        cases o₂ with
        | exact g =>
          obtain ⟨⟨b₃, o₃⟩, h₃, h⟩ := Option.bind_eq_some_iff.mp h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have S₁ := IH sh _ _ _ h₁ s hs
          have S₂ := IH sh _ _ _ h₂ s hs
          refine Sound.of_succ (by omega) fun d b => ?_
          simp only [exec, hp]
          constructor
          · refine Res.within.succ ((S₁ d b).1.bind (fun s' r _ hs' =>
              (S₂ d r).1.bind (fun f' r' _ hf' => ?_) le_rfl) (B₂ := b₂ + b₃) le_rfl)
            rw [fits_exact] at hf'; subst hf'
            exact (IH _ _ _ _ h₃ s' hs' d r').1
          · intro hd hb
            exact (S₁ d b).1.bind_ne ((S₁ d b).2 (by omega) (by omega)) (B₂ := b₂ + b₃)
              (fun s' r _ hs' hr => (S₂ d r).1.bind_ne ((S₂ d r).2 (by omega) (by omega))
                (B₂ := b₃) (fun f' r' _ hf' hr' => by
                  rw [fits_exact] at hf'; subst hf'
                  exact (IH _ _ _ _ h₃ s' hs' d r').2 (by omega) hr') (by omega)) (by omega)
        | _ => simp at h
      | wut x =>
        obtain ⟨⟨b₁, o₁⟩, h₁, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have S₁ := IH sh _ _ _ h₁ s hs
        refine Sound.of_succ (by omega) fun d b => ?_
        simp only [exec, hp]
        refine ⟨Res.within.succ ((S₁ d b).1.bind (B₂ := 0) (fun v r _ hv =>
          ⟨wutShape_sound hv, by omega⟩) (by omega)), fun hd hb => ?_⟩
        exact (S₁ d b).1.bind_ne ((S₁ d b).2 (by omega) (by omega)) (B₂ := 0)
          (fun _ _ _ _ _ => by simp) (by omega)
      | lus x =>
        obtain ⟨⟨b₁, o₁⟩, h₁, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have S₁ := IH sh _ _ _ h₁ s hs
        refine Sound.of_succ (by omega) fun d b => ?_
        simp only [exec, hp]
        refine ⟨Res.within.succ ((S₁ d b).1.bind (B₂ := 0) (fun v r _ hv => ?_) (by omega)),
          fun hd hb => ?_⟩
        · cases v with
          | atom n => exact ⟨lusShape_sound hv, by omega⟩
          | cell _ _ => show r ≤ r + 0; omega
        · exact (S₁ d b).1.bind_ne ((S₁ d b).2 (by omega) (by omega)) (B₂ := 0)
            (fun v _ _ _ _ => by cases v <;> simp) (by omega)
      | tis x y =>
        obtain ⟨⟨b₁, o₁⟩, h₁, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨b₂, o₂⟩, h₂, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have S₁ := IH sh _ _ _ h₁ s hs
        have S₂ := IH sh _ _ _ h₂ s hs
        refine Sound.of_succ (by omega) fun d b => ?_
        simp only [exec, hp]
        refine ⟨Res.within.succ ((S₁ d b).1.bind (fun v r _ hv =>
          (S₂ d r).1.bind (B₂ := 0) (fun w r' _ hw => ⟨tisShape_sound hv hw, by omega⟩)
            (by omega)) le_rfl),
          fun hd hb => ?_⟩
        exact (S₁ d b).1.bind_ne ((S₁ d b).2 (by omega) (by omega)) (B₂ := b₂)
          (fun _ r _ _ hr => (S₂ d r).1.bind_ne ((S₂ d r).2 (by omega) hr) (B₂ := 0)
            (fun _ _ _ _ _ => by simp) (by omega)) (by omega)
      | six x y z =>
        obtain ⟨⟨b₁, o₁⟩, h₁, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨by₁, oy⟩, hy, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨bz, oz⟩, hz, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq, Prod.mk.injEq] at h hy hz
        obtain ⟨rfl, rfl⟩ := h
        have S₁ := IH sh _ _ _ h₁ s hs
        have hac : ∀ w B k, acostWith O D sh w = some (B, .exact k) → Sound B (.exact k) s w :=
          fun w B k hw => IH sh w B _ hw s hs
        -- the arm taken on a yes / a no
        have armY : ∀ d b v r, exec d b s x = .ok v r → v = .atom 0 → Sound by₁ oy s y := by
          intro d b v r hx hv
          have h0 : mayBe 0 o₁ = true := by
            have := ((S₁ d b).1); rw [hx] at this; subst hv; exact mayBe_sound this.1
          rw [h0] at hy; simp only [if_true] at hy
          exact IH _ _ _ _ hy s ((sixSubjects_sound hac hs hx).1 hv)
        have armZ : ∀ d b v r, exec d b s x = .ok v r → v = .atom 1 → Sound bz oz s z := by
          intro d b v r hx hv
          have h1 : mayBe 1 o₁ = true := by
            have := ((S₁ d b).1); rw [hx] at this; subst hv; exact mayBe_sound this.1
          rw [h1] at hz; simp only [if_true] at hz
          exact IH _ _ _ _ hz s ((sixSubjects_sound hac hs hx).2 hv)
        refine Sound.of_succ (by omega) fun d b => ?_
        simp only [exec, hp]
        constructor
        · refine Res.within.succ ((S₁ d b).1.bind (B₂ := max by₁ bz) (fun v r hx hv => ?_) le_rfl)
          rcases v with (_ | _ | n) | _
          · have hY := armY d b _ r hx rfl
            have h0 : mayBe 0 o₁ = true := mayBe_sound hv
            exact (hY d r).1.mono (Nat.le_max_left _ _) fun u hu => by
              unfold sixOut; rw [h0]; simp only [if_true]
              split
              · exact join_sound _ _ _ _ (Or.inl hu)
              · exact hu
          · have hZ := armZ d b _ r hx rfl
            have h1 : mayBe 1 o₁ = true := mayBe_sound hv
            exact (hZ d r).1.mono (Nat.le_max_right _ _) fun u hu => by
              unfold sixOut; rw [h1]; simp only [if_true]
              split
              · exact join_sound _ _ _ _ (Or.inr hu)
              · exact hu
          · show r ≤ r + max by₁ bz; omega
          · show r ≤ r + max by₁ bz; omega
        · intro hd hb
          refine (S₁ d b).1.bind_ne ((S₁ d b).2 (by omega) (by omega)) (B₂ := max by₁ bz)
            (fun v r hx hv hr => ?_) (by omega)
          rcases v with (_ | _ | n) | _
          · exact ((armY d b _ r hx rfl) d r).2 (by omega) (by omega)
          · exact ((armZ d b _ r hx rfl) d r).2 (by omega) (by omega)
          · simp
          · simp
      | seven x y =>
        obtain ⟨⟨b₁, o₁⟩, h₁, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨b₂, o₂⟩, h₂, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have S₁ := IH sh _ _ _ h₁ s hs
        refine Sound.of_succ (by omega) fun d b => ?_
        simp only [exec, hp]
        refine ⟨Res.within.succ ((S₁ d b).1.bind (fun s' r _ hs' =>
          (IH _ _ _ _ h₂ s' hs' d r).1) le_rfl), fun hd hb => ?_⟩
        exact (S₁ d b).1.bind_ne ((S₁ d b).2 (by omega) (by omega)) (B₂ := b₂)
          (fun s' r _ hs' hr => (IH _ _ _ _ h₂ s' hs' d r).2 (by omega) hr) (by omega)
      | eight x y =>
        obtain ⟨⟨b₁, o₁⟩, h₁, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨b₂, o₂⟩, h₂, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have S₁ := IH sh _ _ _ h₁ s hs
        have hcs : ∀ p, fits p o₁ = true → fits (.cell p s) (.cell o₁ sh) = true := fun p hp' => by
          simp [fits, hp', hs]
        refine Sound.of_succ (by omega) fun d b => ?_
        simp only [exec, hp]
        refine ⟨Res.within.succ ((S₁ d b).1.bind (fun p r _ hp' =>
          (IH _ _ _ _ h₂ _ (hcs p hp') d r).1) le_rfl), fun hd hb => ?_⟩
        exact (S₁ d b).1.bind_ne ((S₁ d b).2 (by omega) (by omega)) (B₂ := b₂)
          (fun p r _ hp' hr => (IH _ _ _ _ h₂ _ (hcs p hp') d r).2 (by omega) hr) (by omega)
      | nine a c =>
        obtain ⟨⟨b₁, o₁⟩, h₁, h⟩ := Option.bind_eq_some_iff.mp h
        simp only at h
        cases hg : sAxis a o₁ with
        | exact g =>
          rw [hg] at h
          obtain ⟨⟨b₂, o₂⟩, h₂, h⟩ := Option.bind_eq_some_iff.mp h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have S₁ := IH sh _ _ _ h₁ s hs
          refine Sound.of_succ (by omega) fun d b => ?_
          simp only [exec, hp]
          constructor
          · refine Res.within.succ ((S₁ d b).1.bind (B₂ := b₂) (fun core r _ hcore => ?_) le_rfl)
            cases hax : axis a core with
            | some f' =>
              have hf' := sAxis_sound hcore hax
              rw [hg, fits_exact] at hf'; subst hf'
              exact (IH _ _ _ _ h₂ core hcore d r).1
            | none => show r ≤ r + b₂; omega
          · intro hd hb
            refine (S₁ d b).1.bind_ne ((S₁ d b).2 (by omega) (by omega)) (B₂ := b₂)
              (fun core r _ hcore hr => ?_) (by omega)
            cases hax : axis a core with
            | some f' =>
              have hf' := sAxis_sound hcore hax
              rw [hg, fits_exact] at hf'; subst hf'
              exact (IH _ _ _ _ h₂ core hcore d r).2 (by omega) hr
            | none => simp
        | _ => rw [hg] at h; simp at h
      | ten a c z =>
        obtain ⟨⟨b₁, o₁⟩, h₁, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨b₂, o₂⟩, h₂, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have S₁ := IH sh _ _ _ h₁ s hs
        have S₂ := IH sh _ _ _ h₂ s hs
        refine Sound.of_succ (by omega) fun d b => ?_
        simp only [exec, hp]
        constructor
        · refine Res.within.succ ((S₁ d b).1.bind (fun t r _ ht =>
            (S₂ d r).1.bind (B₂ := 0) (fun p r' _ hpp => ?_) (by omega)) le_rfl)
          cases he : edit a p t with
          | some v => exact ⟨sEdit_sound hpp ht he, by omega⟩
          | none => show r' ≤ r' + 0; omega
        · intro hd hb
          exact (S₁ d b).1.bind_ne ((S₁ d b).2 (by omega) (by omega)) (B₂ := b₂)
            (fun _ r _ _ hr => (S₂ d r).1.bind_ne ((S₂ d r).2 (by omega) hr) (B₂ := 0)
              (fun p r' _ _ _ => by split <;> simp) (by omega)) (by omega)
      | hintS tag z =>
        obtain ⟨⟨b₁, o₁⟩, h₁, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have S₁ := IH sh _ _ _ h₁ s hs
        refine Sound.of_succ (by omega) fun d b => ?_
        simp only [exec, hp]
        exact ⟨Res.within.succ (S₁ d b).1, fun hd hb => (S₁ d b).2 (by omega) (by omega)⟩
      | hintD tag c z =>
        obtain ⟨⟨b₁, o₁⟩, h₁, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨b₂, o₂⟩, h₂, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have S₁ := IH sh _ _ _ h₁ s hs
        have S₂ := IH sh _ _ _ h₂ s hs
        refine Sound.of_succ (by omega) fun d b => ?_
        simp only [exec, hp]
        refine ⟨Res.within.succ ((S₁ d b).1.bind (fun _ r _ _ => (S₂ d r).1) le_rfl),
          fun hd hb => ?_⟩
        exact (S₁ d b).1.bind_ne ((S₁ d b).2 (by omega) (by omega)) (B₂ := b₂)
          (fun _ r _ _ hr => (S₂ d r).2 (by omega) hr) (by omega)

/-- NC-1's interpreter (no summaries) is sound. -/
theorem acost_sound (D : Nat) (sh : Shape) (f : Noun) (B : Nat) (o : Shape)
    (h : acost D sh f = some (B, o)) (s : Noun) (hs : fits s sh = true) : Sound B o s f :=
  acostWith_sound noSummaries_sound D sh f B o h s hs

/-- **`cost_sound`.** A bound `cost` gives is a price: on every subject of the declared shape, a
run given at least `B` fuel does not exhaust, and the metered count is at most `B` — whatever
fuel above `B` it is given. -/
theorem cost_sound {sh : Shape} {f s : Noun} {B : Nat} (h : cost sh f = some B)
    (hs : HasShape s sh) : ∀ fuel, B ≤ fuel →
      Nock.run fuel s f ≠ .error .exhausted ∧ Nock.steps fuel s f ≤ B := by
  intro fuel hfuel
  unfold cost at h
  obtain ⟨⟨B', o⟩, ha, hB⟩ := Option.map_eq_some_iff.mp h
  simp only at hB; subst hB
  have S := acost_sound _ _ _ _ _ ha s hs fuel fuel
  have hne := S.2 hfuel hfuel
  refine ⟨fun he => hne (run_eq_exhausted.mp he), ?_⟩
  have hw := S.1
  unfold Nock.steps
  cases hx : exec fuel fuel s f with
  | ok v r => rw [hx] at hw; dsimp only; have := hw.2; omega
  | crash r => rw [hx] at hw; simp only [Res.within] at hw; dsimp only; omega
  | exhausted => exact absurd hx hne

/-- The form EVAL §3 proposed, at fuel exactly the bound. -/
theorem cost_sound_at_bound {sh : Shape} {f s : Noun} {B : Nat} (h : cost sh f = some B)
    (hs : HasShape s sh) : Nock.run B s f ≠ .error .exhausted ∧ Nock.steps B s f ≤ B :=
  cost_sound h hs B le_rfl

/-- The bound also covers the term's own count: whatever fuel a finished run had, its steps are
at most `B` (with `steps_stable`, every finished run of `f` on `s` costs the same). -/
theorem cost_bounds_every_finished_run {sh : Shape} {f s : Noun} {B : Nat} (h : cost sh f = some B)
    (hs : HasShape s sh) {fuel : Nat} (hfin : Nock.run fuel s f ≠ .error .exhausted) :
    Nock.steps fuel s f ≤ B := by
  rcases Nat.le_total B fuel with hle | hle
  · exact (cost_sound h hs fuel hle).2
  · rw [← steps_stable hfin hle]; exact (cost_sound h hs B le_rfl).2

/-! ## Poles: the decrement of the Urbit docs (`decF`, 36 steps on `3`)

`decF` is a value-indexed loop: its step count is the VALUE of its subject. On an exact subject the
bound is the count; on an interval it is the count at the interval's worst point; on `0` (where it
never stops) nothing bounds it. -/

/-- The exact subject: the bound is the measured count (`pole_decrement_steps = 36`). -/
theorem pole_decrement_exact : cost (.exact (.atom 3)) decF = some 36 := by decide +kernel

/-- An interval subject `[1, 3]`: the bound is the count at `3`, the dearest point. -/
theorem pole_decrement_range : cost (.range 1 3) decF = some 36 := by decide +kernel

/-- `[1, 3]` holds `1`, `2` and `3`; `decF` on `1` is far cheaper than the bound. -/
theorem pole_decrement_on_one : steps 100 (.atom 1) decF = 12 := by decide +kernel

/-- **The refutable pole.** A bound one step under the count is FALSE: at fuel 35 the run of `decF`
on `3` exhausts. -/
theorem pole_decrement_exhausted_35 : run 35 (.atom 3) decF = .error .exhausted := by
  decide +kernel

/-- So `cost` can never answer 35 there: if it did, `cost_sound` would prove the run above does
not exhaust. This is the theorem that goes red if `cost` under-counts. -/
theorem cost_never_under_counts_decrement : cost (.exact (.atom 3)) decF ≠ some 35 := fun h =>
  (cost_sound h (by decide +kernel) 35 le_rfl).1 pole_decrement_exhausted_35

/-- Nothing bounds a divergent formula: for EVERY shape that admits the loop `[2 [0 1] 0 1]` on
itself, `cost` answers `none` (proved from `cost_sound` and `loop_exhausts`, not computed). -/
theorem cost_loop_outside {sh : Shape} (hs : HasShape loopF sh) : cost sh loopF = none := by
  cases h : cost sh loopF with
  | none => rfl
  | some B => exact absurd (loop_exhausts B) (cost_sound h hs B le_rfl).1

/-! ## Poles: `forge` (K-RAN row 6: op 120 charges 1,345 Lean steps)

`forge.jam` is the k-nock template (pinned `hoonc` at nockchain `cbd9298f`; sha256
`0abb4cd92bdf38ea4efff2c12979e10965dda65f060ffe47b964ea0680ac3532`, 566,499 bytes, the whole
stdlib core with forge's gate as arm 2). `forgeSampleJam` is the kernel's sample of K-RAN's
journey run r5 (`kernel-sample.jam`, height 16): `[[16 7 0] ~[['target/0' id] ['inv/iron' 3]
['inv/wood' 2] ['inv/sword' 0]]]`. The run is `*[[P sample] slam(2)]` (`NockRun.subjectFormula`).

These poles evaluate `cue`, `exec` and `acost` over a 566 KB noun, out of reach of the kernel's
reducer, and are `native_decide`: they trust the compiler (flagged). Everything above them is
kernel-checked. -/

def hexNibble (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

def hexBytes (s : String) : List UInt8 :=
  go s.toList
where
  go : List Char → List UInt8
    | a :: b :: rest => UInt8.ofNat (hexNibble a * 16 + hexNibble b) :: go rest
    | _ => []

def forgeJam : List UInt8 := hexBytes (include_str "NockCost" / "forge.jam.hex")

/-- The program: the cue of `forge.jam` (`pole_forge_cues` says it decodes). -/
def forgeProgram : Noun := (cue forgeJam).getD (.atom 0)

def forgeSampleJam : List UInt8 :=
  [5, 131, 225, 91, 128, 158, 46, 76, 238, 172, 140, 238, 5, 6, 8, 208, 231, 151, 49, 37, 93, 72,
   133, 22, 224, 79, 115, 179, 123, 73, 147, 123, 115, 163, 11, 240, 167, 185, 217, 189, 220, 189,
   189, 145, 145, 5, 240, 72, 115, 179, 123, 153, 187, 123, 147, 35, 43]

/-- `'target/0'`, `'inv/iron'`, `'inv/wood'`, `'inv/sword'` as cords. -/
def keyTarget : Nat := 3472121816602009972
def keyIron : Nat := 7957704862680378985
def keyWood : Nat := 7237125683895758441
def keySword : Nat := 1852920348150295064169

def forgeSample : Noun :=
  .cell (.cell (.atom 16) (.cell (.atom 7) (.atom 0)))
    (.cell (.cell (.atom keyTarget) (.atom 11624379191778474484))
      (.cell (.cell (.atom keyIron) (.atom 3))
        (.cell (.cell (.atom keyWood) (.atom 2))
          (.cell (.cell (.atom keySword) (.atom 0)) (.atom 0)))))

theorem forgeSample_cue : cue forgeSampleJam = some forgeSample := by decide +kernel

/-- forge's declared sample shape: the context is anything, the target id any atom, the keys are
the ABI's (fixed at birth), and each field value lies in `[0, iron]`, `[0, wood]`, `[0, sword]`. -/
def forgeSampleShape (iron wood sword : Nat) : Shape :=
  .cell .any
    (.cell (.cell (.exact (.atom keyTarget)) .atom)
      (.cell (.cell (.exact (.atom keyIron)) (.range 0 iron))
        (.cell (.cell (.exact (.atom keyWood)) (.range 0 wood))
          (.cell (.cell (.exact (.atom keySword)) (.range 0 sword)) (.exact (.atom 0))))))

def forgeShape (iron wood sword : Nat) : Shape :=
  .cell (.exact forgeProgram) (forgeSampleShape iron wood sword)

def forgeSubject : Noun := .cell forgeProgram forgeSample

theorem pole_forge_cues : (cue forgeJam).isSome = true := by native_decide

/-- MEASURED, in Lean: the run op 120 charged (K-RAN row 6) is 1,345 steps. -/
theorem pole_forge_steps : steps 4096 forgeSubject (slam 2) = 1345 := by native_decide

theorem forge_sample_fits : HasShape forgeSubject (forgeShape 3 2 0) := by native_decide

/-- **THE NUMBER.** With each field bounded by the sample's own value, the bound is 1,345: ratio
1.00 against the measured count. -/
theorem pole_forge_bound : cost (forgeShape 3 2 0) (slam 2) = some 1345 := by native_decide

/-- Every field in `[0, 3]`: 1,365 (= the count at iron = wood = sword = 3). -/
theorem pole_forge_bound_3 : cost (forgeShape 3 3 3) (slam 2) = some 1365 := by native_decide

/-- Every field in `[0, 25]`: 2,685 — the widest uniform range still within 2× of 1,345. -/
theorem pole_forge_bound_25 : cost (forgeShape 25 25 25) (slam 2) = some 2685 := by native_decide

/-- Every field in `[0, 1000]`: 61,185 — `1185 + 60·V`, linear in the declared maximum, because
`gte`/`sub`/`dec` run unjetted and their step counts are the values. -/
theorem pole_forge_bound_1000 : cost (forgeShape 1000 1000 1000) (slam 2) = some 61185 := by
  native_decide

/-- The price, as a theorem: every sample of forge's shape runs in at most 1,345 steps. -/
theorem forge_priced {s : Noun} (hs : HasShape s (forgeShape 3 2 0)) (fuel : Nat) (h : 1345 ≤ fuel) :
    run fuel s (slam 2) ≠ .error .exhausted ∧ steps fuel s (slam 2) ≤ 1345 :=
  cost_sound pole_forge_bound hs fuel h

/-! ## Axioms

Every theorem above the forge poles rests on the standard three only (`#assert_axioms` refuses
`sorryAx` and the compiler trust). The forge poles are `native_decide` and say so in their pins. -/

open Minidregg.Theory.AssertAxioms

#assert_axioms axisAux_fuel
#assert_axioms axis_step
#assert_axioms editAux_self
#assert_axioms edit_self
#assert_axioms split_sound
#assert_axioms sAxisAux_sound
#assert_axioms sAxis_sound
#assert_axioms sEditAux_sound
#assert_axioms sEdit_sound
#assert_axioms asRange_sound
#assert_axioms isAtomic_sound
#assert_axioms asCell_sound
#assert_axioms joinStep_sound
#assert_axioms isBot_sound
#assert_axioms join_sound
#assert_axioms eqDecideS_sound
#assert_axioms eqDecide_sound
#assert_axioms tisShape_sound
#assert_axioms wutShape_sound
#assert_axioms lusShape_sound
#assert_axioms mayBe_sound
#assert_axioms neShape_sound
#assert_axioms testAxis_some
#assert_axioms Res.within.bind
#assert_axioms Res.within.bind_ne
#assert_axioms Res.within.mono
#assert_axioms Res.within.succ
#assert_axioms Sound.of_succ
#assert_axioms noSummaries_sound
#assert_axioms acostWith_sound
#assert_axioms sixSubjects_sound
#assert_axioms acost_sound
#assert_axioms cost_sound
#assert_axioms cost_sound_at_bound
#assert_axioms cost_bounds_every_finished_run
#assert_axioms pole_decrement_exact
#assert_axioms pole_decrement_range
#assert_axioms pole_decrement_on_one
#assert_axioms pole_decrement_exhausted_35
#assert_axioms cost_never_under_counts_decrement
#assert_axioms cost_loop_outside
#assert_axioms forgeSample_cue

/-- info: 'Minidregg.Theory.NockCost.pole_forge_cues' depends on axioms: [propext, Classical.choice, Quot.sound, pole_forge_cues._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms pole_forge_cues
/-- info: 'Minidregg.Theory.NockCost.pole_forge_steps' depends on axioms: [propext, Classical.choice, Quot.sound, pole_forge_steps._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms pole_forge_steps
/-- info: 'Minidregg.Theory.NockCost.forge_sample_fits' depends on axioms: [propext, Classical.choice, Quot.sound, forge_sample_fits._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms forge_sample_fits
/-- info: 'Minidregg.Theory.NockCost.pole_forge_bound' depends on axioms: [propext, Classical.choice, Quot.sound, pole_forge_bound._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms pole_forge_bound
/-- info: 'Minidregg.Theory.NockCost.pole_forge_bound_3' depends on axioms: [propext, Classical.choice, Quot.sound, pole_forge_bound_3._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms pole_forge_bound_3
/-- info: 'Minidregg.Theory.NockCost.pole_forge_bound_25' depends on axioms: [propext, Classical.choice, Quot.sound, pole_forge_bound_25._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms pole_forge_bound_25
/-- info: 'Minidregg.Theory.NockCost.pole_forge_bound_1000' depends on axioms: [propext, Classical.choice, Quot.sound, pole_forge_bound_1000._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms pole_forge_bound_1000
/-- info: 'Minidregg.Theory.NockCost.forge_priced' depends on axioms: [propext, Classical.choice, Quot.sound, pole_forge_bound._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms forge_priced

end NockCost
end Minidregg.Theory
