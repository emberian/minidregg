/- Templates over rigid Self/Super (OB-LTUO LT2, docs/objective-bend/MODULAR-TYPING.md §6).

Step 2: `canonical_instantiate`. The checker compares types by `Ty.canonical` (sorted
rows, first field of a name wins). A template is checked with rigid variables and
emitted at instances `τ.instantiate σ`; for a conversion the template's checker
accepted (`a.canonical = b.canonical`) to remain a conversion at the instance, canonical
form must commute with instantiation up to a final `canonical`:

    (τ.instantiate σ).canonical = (τ.canonical.instantiate σ).canonical

including the override case (a tail instantiated with a row that repeats a listed
field: the listed one, which is first, wins on both sides). No sortedness premise is
needed: `insertCanonical` is first-match, and the two facts it rests on
(`insertCanonical_same`, `insertCanonical_comm`) hold for every row. -/
import Theory.ObjectiveBendTypes
import Theory.ObjectiveBendTyping
import Theory.AxiomPin
namespace Minidregg.Theory.ObjectiveBendTemplates
open ObjectiveBendTypes
set_option autoImplicit false

theorem lt_of_not_lt_ne {a b : String} (h1 : ¬ a < b) (h2 : a ≠ b) : b < a :=
  Decidable.byContradiction fun h3 => h2 (String.le_antisymm (String.not_lt.mp h3) (String.not_lt.mp h1))

theorem tri {a b : String} (h : a ≠ b) : (a < b ∧ ¬ b < a) ∨ (b < a ∧ ¬ a < b) := by
  by_cases l : a < b
  · exact .inl ⟨l, String.lt_asymm l⟩
  · have g := lt_of_not_lt_ne l h
    exact .inr ⟨g, l⟩

/-- Inserting a name twice keeps the second insertion. -/
theorem insertCanonical_same (row : Ty) (name : String) (first second : Ty) :
    (row.insertCanonical name first).insertCanonical name second = row.insertCanonical name second := by
  induction row with
  | field prior old tail _ ih =>
    by_cases he : name = prior
    · subst he; simp [Ty.insertCanonical]
    · by_cases hl : name < prior
      · simp [Ty.insertCanonical, he, hl]
      · simp [Ty.insertCanonical, he, hl, ih]
  | _ => simp [Ty.insertCanonical]

/-- Inserting two different names commutes. -/
theorem insertCanonical_comm (row : Ty) (n p : String) (a b : Ty) (ne : n ≠ p) :
    (row.insertCanonical n a).insertCanonical p b = (row.insertCanonical p b).insertCanonical n a := by
  have ne' : p ≠ n := fun h => ne h.symm
  induction row with
  | field q o t _ ih =>
    by_cases hn : n = q
    · subst hn
      by_cases hp : p < n
      · simp [Ty.insertCanonical, ne, ne', hp, String.lt_asymm hp]
      · have : n < p := lt_of_not_lt_ne hp ne'
        simp [Ty.insertCanonical, ne', hp]
    · by_cases hp : p = q
      · subst hp
        by_cases hl : n < p
        · simp [Ty.insertCanonical, ne, ne', hl, String.lt_asymm hl]
        · simp [Ty.insertCanonical, ne, hl]
      · have hp' : q ≠ p := fun h => hp h.symm
        rcases tri hn with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases tri hp with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
          rcases tri ne with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
          simp [Ty.insertCanonical, a1, a2, b1, b2, c1, c2, hn, hp, hp', ne, ne', ih] <;>
          first
          | exact absurd (String.lt_trans (String.lt_trans ‹_› ‹_›) ‹_›) (String.lt_irrefl _)
          | skip
  | _ =>
    by_cases hl : n < p
    · simp [Ty.insertCanonical, ne, ne', hl, String.lt_asymm hl]
    · have hl' : p < n := lt_of_not_lt_ne hl ne
      simp [Ty.insertCanonical, ne, ne', hl, hl']

theorem canonical_instantiate_insert (σ : Nat → Ty) (row : Ty) (name : String) (member : Ty) :
    ((row.insertCanonical name member).instantiate σ).canonical =
      ((row.instantiate σ).canonical).insertCanonical name ((member.instantiate σ).canonical) := by
  induction row with
  | field prior old tail _ ih =>
    by_cases he : name = prior
    · subst he
      simp [Ty.insertCanonical, Ty.instantiate, Ty.canonical, insertCanonical_same]
    · by_cases hl : name < prior
      · simp [Ty.insertCanonical, he, hl, Ty.instantiate, Ty.canonical]
      · simp only [Ty.insertCanonical, he, hl, if_false, Ty.instantiate, Ty.canonical]
        rw [ih, insertCanonical_comm _ _ _ _ _ he]
  | _ => simp [Ty.insertCanonical, Ty.instantiate, Ty.canonical]

/-- Canonical form commutes with instantiation, up to a final `canonical`. -/
theorem canonical_instantiate (σ : Nat → Ty) (type : Ty) :
    (type.instantiate σ).canonical = (type.canonical.instantiate σ).canonical := by
  induction type with
  | field name member tail ihm iht =>
    simp only [Ty.instantiate, Ty.canonical]
    rw [canonical_instantiate_insert, ← iht, ← ihm]
  | arrow reuse q d c ihd ihc => simp [Ty.instantiate, Ty.canonical, ihd, ihc]
  | specification m e ihm ihe => simp [Ty.instantiate, Ty.canonical, ihm, ihe]
  | prototype s t ihs iht => simp [Ty.instantiate, Ty.canonical, ihs, iht]
  | variant r ih => simp [Ty.instantiate, Ty.canonical, ih]
  | computation p r a ihp ihr iha => simp [Ty.instantiate, Ty.canonical, ihp, ihr, iha]
  | _ => simp [Ty.instantiate, Ty.canonical]

/-- So a conversion the template's checker accepted survives every instantiation. -/
theorem canonical_eq_instantiate (σ : Nat → Ty) {a b : Ty} (h : a.canonical = b.canonical) :
    (a.instantiate σ).canonical = (b.instantiate σ).canonical := by
  rw [canonical_instantiate σ a, canonical_instantiate σ b, h]

#assert_axioms insertCanonical_same insertCanonical_comm canonical_instantiate_insert canonical_instantiate
  canonical_eq_instantiate

/-! ## Step 4: a template checked against its rigid bounds is accepted at every discharge

`infer_instantiate` (MODULAR-TYPING §6). A template is checked by `infer` under assumptions
whose `rigid` variables are its `Self` (a lower bound, never an alias). An instance is the
SAME term with every annotation and every context type instantiated by `σ`, checked under
the instance's assumptions. If `σ` discharges the bounds (`Discharges`), the instance is
accepted and its type is the template's type instantiated. `extra` is the instance's
additional lookup depth (a wider row may hide a member deeper than the bound did). -/

open ObjectiveBendTyping ObjectiveBendOpenRecursion

def instantiateAnnotation (σ : Nat → Ty) (annotation : LambdaAnnotation) : LambdaAnnotation :=
  { annotation with domain := annotation.domain.instantiate σ, codomain := annotation.codomain.instantiate σ }

def instantiateAnnotations (σ : Nat → Ty) (annotations : Annotations) : Annotations :=
  fun position => (annotations position).map (instantiateAnnotation σ)

def instantiateContext (σ : Nat → Ty) (context : Context) : Context :=
  context.map fun binding => ⟨binding.type.instantiate σ, binding.quantity⟩

/-- What an instance must discharge. Non-rigid variables are left alone and keep their
bounds (which mention no rigid variable); each rigid variable's image supports its bound
(every member the bound discloses, at the bound's member type instantiated, and row-ness),
is shareable exactly when the template assumed it shareable, and is never an activity. -/
structure Discharges (σ : Nat → Ty) (template instance_ : Assumptions) (extra : Nat) : Prop where
  fixed : ∀ j, j ∉ template.rigid → σ j = .variable j
  bounds : ∀ j, j ∉ template.rigid → instance_.bounds.lookup j = template.bounds.lookup j
  aliases : ∀ j, j ∉ template.rigid → instance_.alias j = template.alias j
  closed : ∀ j bound, j ∉ template.rigid → template.bounds.lookup j = some bound → bound.instantiate σ = bound
  lookup : ∀ k bound, k ∈ template.rigid → template.bounds.lookup k = some bound →
    ∀ fuel name member, bound.lookup template.bounds fuel name = some member →
      (σ k).lookup instance_.bounds (fuel + extra) name = some (member.instantiate σ)
  row : ∀ k bound, k ∈ template.rigid → template.bounds.lookup k = some bound →
    ∀ fuel, bound.isRow template.bounds fuel = true → (σ k).isRow instance_.bounds (fuel + extra) = true
  shareable : ∀ j, (σ j).shareableUnder instance_.shareableVariables = template.shareableVariables.contains j
  pure : ∀ j, (σ j).isComputation = false

section
variable {σ : Nat → Ty} {template instance_ : Assumptions} {extra : Nat}

theorem alias_not_rigid {assumptions : Assumptions} {j : Nat} {bound : Ty}
    (found : assumptions.alias j = some bound) : j ∉ assumptions.rigid := by
  intro member
  have : assumptions.rigid.contains j = true := by simpa using member
  rw [Assumptions.alias_rigid this] at found
  cases found

theorem instantiate_isComputation (pure : ∀ j, (σ j).isComputation = false) (type : Ty) :
    (type.instantiate σ).isComputation = type.isComputation := by
  cases type with
  | «variable» j => exact pure j
  | _ => simp [Ty.instantiate, Ty.isComputation]

theorem shareableUnder_instantiate {vars vars' : List Nat}
    (shareable : ∀ j, (σ j).shareableUnder vars' = vars.contains j) (type : Ty) :
    (type.instantiate σ).shareableUnder vars' = type.shareableUnder vars := by
  induction type with
  | «variable» j => simp [Ty.instantiate, Ty.shareableUnder, shareable]
  | field _ m t ihm iht => simp [Ty.instantiate, Ty.shareableUnder, ihm, iht]
  | specification m e ihm ihe => simp [Ty.instantiate, Ty.shareableUnder, ihm, ihe]
  | prototype s t ihs iht => simp [Ty.instantiate, Ty.shareableUnder, ihs, iht]
  | variant r ih => simp [Ty.instantiate, Ty.shareableUnder, ih]
  | _ => simp [Ty.instantiate, Ty.shareableUnder, Ty.shareable]

theorem instantiate_of_isData {type : Ty} (data : type.isData = true) : type.instantiate σ = type := by
  induction type with
  | field _ m t ihm iht =>
    simp only [Ty.isData, Bool.and_eq_true] at data
    simp [Ty.instantiate, ihm data.1, iht data.2]
  | variant r ih => simp only [Ty.isData] at data; simp [Ty.instantiate, ih data]
  | «variable» _ => simp [Ty.isData] at data
  | arrow => simp [Ty.isData] at data
  | specification => simp [Ty.isData] at data
  | prototype => simp [Ty.isData] at data
  | computation => simp [Ty.isData] at data
  | _ => rfl

theorem isPlan_instantiate {type : Ty} (plan : type.isPlan = true) : type.instantiate σ = type := by
  cases type <;> simp [Ty.isPlan] at plan
  exact instantiate_of_isData (type := .variant _) (by simpa [Ty.isData] using plan)

theorem callable_instantiate {type : Ty} {reuse : Reuse} {quantity : Quantity} {domain codomain : Ty}
    (shape : callable type = .arrow reuse quantity domain codomain) :
    callable (type.instantiate σ) = .arrow reuse quantity (domain.instantiate σ) (codomain.instantiate σ) := by
  induction type with
  | arrow r q d c =>
    simp only [callable] at shape; cases shape; rfl
  | specification m e _ ihe => simp only [callable] at shape; simpa [Ty.instantiate, callable] using ihe shape
  | _ => simp [callable] at shape

theorem instantiateContext_length (context : Context) :
    (instantiateContext σ context).length = context.length := by simp [instantiateContext]

theorem zeroUses_instantiate (context : Context) : zeroUses (instantiateContext σ context) = zeroUses context := by
  simp [zeroUses, instantiateContext_length]

theorem variableUses_instantiate (context : Context) (index : Nat) :
    variableUses (instantiateContext σ context) index = variableUses context index := by
  simp [variableUses, instantiateContext_length]

theorem safeUses_instantiate (context : Context) (uses : Uses) :
    safeUses (instantiateContext σ context) uses = safeUses context uses := by
  simp only [safeUses, instantiateContext, List.length_map, List.zip_map_left, List.all_map]
  rfl

theorem reusableCaptures_instantiate {vars vars' : List Nat}
    (shareable : ∀ j, (σ j).shareableUnder vars' = vars.contains j) (context : Context) (uses : Uses) :
    reusableCaptures vars' (instantiateContext σ context) uses = reusableCaptures vars context uses := by
  simp only [reusableCaptures, instantiateContext, List.length_map, List.zip_map_left, List.all_map]
  congr 2
  funext pair
  simp [shareableUnder_instantiate shareable]

theorem validContext_instantiate {vars vars' : List Nat}
    (shareable : ∀ j, (σ j).shareableUnder vars' = vars.contains j) (context : Context) :
    validContext vars' (instantiateContext σ context) = validContext vars context := by
  simp only [validContext, instantiateContext, List.all_map]
  congr 1
  funext binding
  simp [shareableUnder_instantiate shareable]

theorem getElem?_instantiateContext (context : Context) (index : Nat) :
    (instantiateContext σ context)[index]? =
      context[index]?.map (fun binding => ⟨binding.type.instantiate σ, binding.quantity⟩) := by
  simp [instantiateContext]

theorem instantiateContext_cons (type : Ty) (quantity : Quantity) (context : Context) :
    instantiateContext σ (⟨type, quantity⟩ :: context) = ⟨type.instantiate σ, quantity⟩ :: instantiateContext σ context := rfl


theorem primitiveTypes_instantiate (primitive : Primitive) :
    (primitiveTypes primitive).1.instantiate σ = (primitiveTypes primitive).1 ∧
      (primitiveTypes primitive).2.instantiate σ = (primitiveTypes primitive).2 := by
  cases primitive <;> exact ⟨rfl, rfl⟩

theorem overlay_instantiate {row : Ty} (closed : row.tail = .emptyRow) (inherited : Ty) :
    (overlay row inherited).instantiate σ = overlay (row.instantiate σ) (inherited.instantiate σ) := by
  induction row with
  | field n m t _ iht => simp only [Ty.tail] at closed; simp [overlay, Ty.instantiate, iht closed]
  | emptyRow => rfl
  | _ => simp [Ty.tail] at closed

theorem inferFields_tail {assumptions : Assumptions} {annotations : Annotations} {context : Context}
    {position : List Nat} : ∀ {fuel : Nat} {index : Nat} {fields : List (String × Term)}
    {result : InferredFields assumptions context fields},
    inferFields assumptions annotations context position index fuel fields = some result → result.type.tail = .emptyRow
  | 0, _, _, _, h => by simp [inferFields] at h
  | fuel + 1, index, [], result, h => by simp only [inferFields] at h; cases h; rfl
  | fuel + 1, index, (name, body) :: rest, result, h => by
    simp only [inferFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨first, _, later, laterTyped, h⟩ := h
    split at h
    · cases h; simpa [Ty.tail] using inferFields_tail laterTyped
    · cases h

variable (D : Discharges σ template instance_ extra)
include D

theorem Discharges.lookup_instantiate : ∀ (fuel : Nat) (type : Ty) (name : String) (member : Ty),
    type.lookup template.bounds fuel name = some member →
    (type.instantiate σ).lookup instance_.bounds (fuel + extra) name = some (member.instantiate σ)
  | 0, _, _, _, h => by simp [Ty.lookup] at h
  | fuel + 1, type, name, member, h => by
    rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
    cases type with
    | field prior m tail =>
      simp only [Ty.lookup, Ty.instantiate] at h ⊢
      split at h
      · cases h; rw [if_pos ‹_›]
      · rw [if_neg ‹_›]; exact Discharges.lookup_instantiate fuel tail name member h
    | «variable» j =>
      simp only [Ty.lookup, Option.bind_eq_bind] at h
      cases found : template.bounds.lookup j with
      | none => simp [found] at h
      | some bound =>
        simp only [found, Option.bind_some] at h
        by_cases rigid : j ∈ template.rigid
        · exact Ty.lookup_mono (D.lookup j bound rigid found fuel name member h) (by omega)
        · simp only [Ty.instantiate, D.fixed j rigid, Ty.lookup, Option.bind_eq_bind, D.bounds j rigid, found,
            Option.bind_some]
          have := Discharges.lookup_instantiate fuel bound name member h
          rwa [D.closed j bound rigid found] at this
    | _ => simp [Ty.lookup] at h

theorem Discharges.isRow_instantiate : ∀ (fuel : Nat) (type : Ty),
    type.isRow template.bounds fuel = true → (type.instantiate σ).isRow instance_.bounds (fuel + extra) = true
  | 0, _, h => by simp [Ty.isRow] at h
  | fuel + 1, type, h => by
    rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
    cases type with
    | emptyRow => rfl
    | field _ _ tail =>
      simp only [Ty.isRow, Ty.instantiate] at h ⊢
      exact Discharges.isRow_instantiate fuel tail h
    | «variable» j =>
      simp only [Ty.isRow] at h
      cases found : template.bounds.lookup j with
      | none => simp [found] at h
      | some bound =>
        simp only [found] at h
        by_cases rigid : j ∈ template.rigid
        · exact Ty.isRow_mono (D.row j bound rigid found fuel h) (by omega)
        · simp only [Ty.instantiate, D.fixed j rigid, Ty.isRow, D.bounds j rigid, found]
          have := Discharges.isRow_instantiate fuel bound h
          rwa [D.closed j bound rigid found] at this
    | _ => simp [Ty.isRow] at h

theorem Discharges.sameType_instantiate {actual expected : Ty}
    (agreement : sameType template actual expected = true) :
    sameType instance_ (actual.instantiate σ) (expected.instantiate σ) = true := by
  simp only [sameType, Bool.or_eq_true] at agreement ⊢
  rcases agreement with (canonical | aliasActual) | aliasExpected
  · exact .inl (.inl (by simpa using canonical_eq_instantiate σ (by simpa using canonical)))
  · cases actual with
    | «variable» j =>
      left; right
      cases aliased : template.alias j with
      | none => simp [aliased] at aliasActual
      | some bound =>
        have rigid := alias_not_rigid aliased
        have closed := D.closed j bound rigid (Assumptions.alias_bound aliased)
        obtain ⟨pure, equal⟩ : expected.isComputation = false ∧ bound.canonical = expected.canonical := by
          simpa [aliased] using aliasActual
        have equal' : bound.canonical = (expected.instantiate σ).canonical := by
          have := canonical_eq_instantiate σ equal
          rwa [closed] at this
        simp [Ty.instantiate, D.fixed j rigid, D.aliases j rigid, aliased, equal',
          instantiate_isComputation D.pure, pure]
    | _ => simp at aliasActual
  · cases expected with
    | «variable» j =>
      right
      cases aliased : template.alias j with
      | none => simp [aliased] at aliasExpected
      | some bound =>
        have rigid := alias_not_rigid aliased
        have closed := D.closed j bound rigid (Assumptions.alias_bound aliased)
        obtain ⟨pure, equal⟩ : actual.isComputation = false ∧ bound.canonical = actual.canonical := by
          simpa [aliased] using aliasExpected
        have equal' : bound.canonical = (actual.instantiate σ).canonical := by
          have := canonical_eq_instantiate σ equal
          rwa [closed] at this
        simp [Ty.instantiate, D.fixed j rigid, D.aliases j rigid, aliased, equal',
          instantiate_isComputation D.pure, pure]
    | _ => simp at aliasExpected

theorem Discharges.agree_instantiate {actual expected : Ty}
    (agreement : agree template actual expected = true) :
    agree instance_ (actual.instantiate σ) (expected.instantiate σ) = true := by
  simp only [agree, Bool.and_eq_true] at agreement ⊢
  refine ⟨D.sameType_instantiate agreement.1, ?_⟩
  simpa [shareableUnder_instantiate D.shareable] using agreement.2

theorem Discharges.variantRow_instantiate {type row : Ty} (found : variantRow template type = some row) :
    variantRow instance_ (type.instantiate σ) = some (row.instantiate σ) := by
  cases type with
  | variant r => simp [variantRow] at found; subst found; rfl
  | «variable» j =>
    simp only [variantRow] at found
    split at found
    · rename_i r aliased
      cases found
      have rigid := alias_not_rigid aliased
      have closed := D.closed j _ rigid (Assumptions.alias_bound aliased)
      simp only [Ty.instantiate] at closed
      simp [Ty.instantiate, D.fixed j rigid, variantRow, D.aliases j rigid, aliased, Ty.variant.inj closed]
    · cases found
  | _ => simp [variantRow] at found


theorem Discharges.argumentAllowed_instantiate (quantity : Quantity) (context : Context) (type : Ty) (uses : Uses) :
    argumentAllowed instance_ quantity (instantiateContext σ context) (type.instantiate σ) uses =
      argumentAllowed template quantity context type uses := by
  simp [argumentAllowed, instantiate_isComputation D.pure, shareableUnder_instantiate D.shareable,
    reusableCaptures_instantiate D.shareable]

theorem Discharges.reusableAllowed_instantiate (reuse : Reuse) (context : Context) (uses : Uses) :
    reusableAllowed instance_ reuse (instantiateContext σ context) uses = reusableAllowed template reuse context uses := by
  simp [reusableAllowed, reusableCaptures_instantiate D.shareable]

/-- The template theorem (MODULAR-TYPING §6): every term the checker accepts under rigid
bounds is accepted at every instance that discharges them, at the instantiated type, with
the same usage. By induction on fuel, mirroring `infer`, `inferFields`, `inferArms`. -/
theorem Discharges.infer_instantiate : ∀ fuel : Nat,
    (∀ (annotations : Annotations) (context : Context) (position : List Nat) (term : Term)
        (result : Inferred template context term),
      infer template annotations context position fuel term = some result →
      ∃ result' : Inferred instance_ (instantiateContext σ context) term,
        infer instance_ (instantiateAnnotations σ annotations) (instantiateContext σ context) position
          (fuel + extra) term = some result' ∧
        result'.type = result.type.instantiate σ ∧ result'.uses = result.uses) ∧
    (∀ (annotations : Annotations) (context : Context) (position : List Nat) (index : Nat)
        (fields : List (String × Term)) (result : InferredFields template context fields),
      inferFields template annotations context position index fuel fields = some result →
      ∃ result' : InferredFields instance_ (instantiateContext σ context) fields,
        inferFields instance_ (instantiateAnnotations σ annotations) (instantiateContext σ context) position index
          (fuel + extra) fields = some result' ∧
        result'.type = result.type.instantiate σ ∧ result'.uses = result.uses) ∧
    (∀ (annotations : Annotations) (context : Context) (position : List Nat) (index : Nat) (row : Ty)
        (expected : Option Ty) (arms : List (String × Term)) (result : InferredArms template context arms),
      inferArms template annotations context position index row expected fuel arms = some result →
      ∃ result' : InferredArms instance_ (instantiateContext σ context) arms,
        inferArms instance_ (instantiateAnnotations σ annotations) (instantiateContext σ context) position index
          (row.instantiate σ) (expected.map (Ty.instantiate σ)) (fuel + extra) arms = some result' ∧
        result'.row = result.row.instantiate σ ∧ result'.result = result.result.instantiate σ ∧
        result'.uses = result.uses)
  | 0 => ⟨fun _ _ _ _ _ h => by simp [infer] at h, fun _ _ _ _ _ _ h => by simp [inferFields] at h,
      fun _ _ _ _ _ _ _ _ h => by simp [inferArms] at h⟩
  | fuel + 1 => by
    obtain ⟨ih, ihFields, ihArms⟩ := Discharges.infer_instantiate fuel
    rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
    refine ⟨?_, ?_, ?_⟩
    · intro annotations context position term result h
      cases term with
      | bound index =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨binding, found, h⟩ := h
        rw [dif_pos found] at h
        cases h
        have found' := getElem?_instantiateContext (σ := σ) context index
        rw [found, Option.map_some] at found'
        simp only [infer, Option.bind_eq_bind, found', Option.bind_some, dif_pos found']
        exact ⟨_, rfl, rfl, variableUses_instantiate context index⟩
      | nat value =>
        simp only [infer] at h; cases h
        exact ⟨_, rfl, rfl, zeroUses_instantiate context⟩
      | boolean value =>
        simp only [infer] at h; cases h
        exact ⟨_, rfl, rfl, zeroUses_instantiate context⟩
      | label value =>
        simp only [infer] at h; cases h
        exact ⟨_, rfl, rfl, zeroUses_instantiate context⟩
      | lam body =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨annotation, found, inner, innerTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i agreed
        split at h
        rotate_left; · cases h
        rename_i safe
        split at h
        rotate_left; · cases h
        rename_i valid
        split at h
        rotate_left; · cases h
        rename_i captures
        cases h
        obtain ⟨inner', innerTyped', innerType, innerUses⟩ := ih _ _ _ _ _ innerTyped
        have found' : instantiateAnnotations σ annotations position = some (instantiateAnnotation σ annotation) := by
          simp [instantiateAnnotations, found]
        simp only [instantiateContext_cons] at innerTyped'
        simp only [infer, Option.bind_eq_bind, found', Option.bind_some]
        simp only [instantiateAnnotation] at innerTyped' ⊢
        rw [innerTyped', Option.bind_some]
        have a1 : agree instance_ inner'.type (annotation.codomain.instantiate σ) = true := by
          rw [innerType]; exact D.agree_instantiate agreed
        have a2 : safeUses (⟨annotation.domain.instantiate σ, annotation.parameter⟩ :: instantiateContext σ context)
            inner'.uses = true := by
          rw [innerUses, ← instantiateContext_cons, safeUses_instantiate]; exact safe
        have a3 : validContext instance_.shareableVariables
            (⟨annotation.domain.instantiate σ, annotation.parameter⟩ :: instantiateContext σ context) = true := by
          rw [← instantiateContext_cons, validContext_instantiate D.shareable]; exact valid
        have a4 : reusableAllowed instance_ annotation.reuse (instantiateContext σ context) inner'.uses.tail = true := by
          rw [innerUses, D.reusableAllowed_instantiate]; exact captures
        rw [dif_pos a1, dif_pos a2, dif_pos a3, dif_pos a4]
        exact ⟨_, rfl, rfl, congrArg List.tail innerUses⟩
      | app function argument =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨fn, fnTyped, arg, argTyped, h⟩ := h
        obtain ⟨fn', fnTyped', fnType, fnUses⟩ := ih _ _ _ _ _ fnTyped
        obtain ⟨arg', argTyped', argType, argUses⟩ := ih _ _ _ _ _ argTyped
        simp only [infer, Option.bind_eq_bind, fnTyped', argTyped', Option.bind_some]
        split at h
        rotate_left; · cases h
        rename_i reuse quantity domain codomain shape
        split at h
        rotate_left; · cases h
        rename_i agreed
        split at h
        rotate_left; · cases h
        rename_i allowed
        cases h
        have shape' : callable fn'.type = .arrow reuse quantity (domain.instantiate σ) (codomain.instantiate σ) := by
          rw [fnType]; exact callable_instantiate shape
        split
        · rename_i reuse' quantity' domain' codomain' shape''
          rw [shape'] at shape''
          cases shape''
          have a1 : agree instance_ arg'.type (domain.instantiate σ) = true := by
            rw [argType]; exact D.agree_instantiate agreed
          have a2 : argumentAllowed instance_ quantity (instantiateContext σ context) (domain.instantiate σ)
              arg'.uses = true := by
            rw [argUses, D.argumentAllowed_instantiate]; exact allowed
          rw [dif_pos a1, dif_pos a2]
          exact ⟨_, rfl, rfl, by dsimp only; rw [fnUses, argUses]⟩
        · rename_i other
          exact (other _ _ _ _ shape').elim
      | record fields =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨members, membersTyped, h⟩ := h
        cases h
        obtain ⟨members', membersTyped', membersType, membersUses⟩ := ihFields _ _ _ _ _ _ membersTyped
        simp only [infer, Option.bind_eq_bind, membersTyped', Option.bind_some]
        exact ⟨_, rfl, membersType, membersUses⟩
      | get target name =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨prior, priorTyped, member, found, h⟩ := h
        rw [dif_pos found] at h
        cases h
        obtain ⟨prior', priorTyped', priorType, priorUses⟩ := ih _ _ _ _ _ priorTyped
        have found' : prior'.type.lookup instance_.bounds (fuel + extra + 1) name = some (member.instantiate σ) := by
          rw [priorType, show fuel + extra + 1 = fuel + 1 + extra by omega]
          exact D.lookup_instantiate _ _ _ _ found
        simp only [infer, Option.bind_eq_bind, priorTyped', Option.bind_some, found', dif_pos found']
        exact ⟨_, rfl, rfl, priorUses⟩
      | extend target fields =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨prior, priorTyped, members, membersTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i isRow
        cases h
        obtain ⟨prior', priorTyped', priorType, priorUses⟩ := ih _ _ _ _ _ priorTyped
        obtain ⟨members', membersTyped', membersType, membersUses⟩ := ihFields _ _ _ _ _ _ membersTyped
        have isRow' : prior'.type.isRow instance_.bounds (fuel + extra + 64) = true := by
          rw [priorType, show fuel + extra + 64 = fuel + 64 + extra by omega]
          exact D.isRow_instantiate _ _ isRow
        simp only [infer, Option.bind_eq_bind, priorTyped', membersTyped', Option.bind_some, dif_pos isRow']
        refine ⟨_, rfl, ?_, by dsimp only; rw [priorUses, membersUses]⟩
        show overlay members'.type prior'.type = _
        rw [membersType, priorType, overlay_instantiate (inferFields_tail membersTyped)]
      | specification metadata extension =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨descriptor, descriptorTyped, body, bodyTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i pureDescriptor
        split at h
        rotate_left; · cases h
        rename_i pureBody
        cases h
        obtain ⟨d', dTyped', dType, dUses⟩ := ih _ _ _ _ _ descriptorTyped
        obtain ⟨b', bTyped', bType, bUses⟩ := ih _ _ _ _ _ bodyTyped
        have p1 : d'.type.isComputation = false := by rw [dType, instantiate_isComputation D.pure]; exact pureDescriptor
        have p2 : b'.type.isComputation = false := by rw [bType, instantiate_isComputation D.pure]; exact pureBody
        simp only [infer, Option.bind_eq_bind, dTyped', bTyped', Option.bind_some, dif_pos p1, dif_pos p2]
        exact ⟨_, rfl, by simp [dType, bType, Ty.instantiate], by dsimp only; rw [dUses, bUses]⟩
      | prototype spec target =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨code, codeTyped, value, valueTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i pureCode
        split at h
        rotate_left; · cases h
        rename_i pureValue
        cases h
        obtain ⟨c', cTyped', cType, cUses⟩ := ih _ _ _ _ _ codeTyped
        obtain ⟨v', vTyped', vType, vUses⟩ := ih _ _ _ _ _ valueTyped
        have p1 : c'.type.isComputation = false := by rw [cType, instantiate_isComputation D.pure]; exact pureCode
        have p2 : v'.type.isComputation = false := by rw [vType, instantiate_isComputation D.pure]; exact pureValue
        simp only [infer, Option.bind_eq_bind, cTyped', vTyped', Option.bind_some, dif_pos p1, dif_pos p2]
        exact ⟨_, rfl, by simp [cType, vType, Ty.instantiate], by dsimp only; rw [cUses, vUses]⟩
      | reflect target =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨inner, innerTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i specType targetType shape
        cases h
        obtain ⟨inner', innerTyped', innerType, innerUses⟩ := ih _ _ _ _ _ innerTyped
        simp only [infer, Option.bind_eq_bind, innerTyped', Option.bind_some]
        rw [shape] at innerType
        split
        · rename_i s' t' shape'
          rw [innerType] at shape'
          simp only [Ty.instantiate, Ty.prototype.injEq] at shape'
          obtain ⟨rfl, rfl⟩ := shape'
          exact ⟨_, rfl, rfl, innerUses⟩
        · rename_i other
          exact (other _ _ (by rw [innerType]; rfl)).elim
      | metadata target =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨inner, innerTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i metadataType extensionType shape
        cases h
        obtain ⟨inner', innerTyped', innerType, innerUses⟩ := ih _ _ _ _ _ innerTyped
        simp only [infer, Option.bind_eq_bind, innerTyped', Option.bind_some]
        rw [shape] at innerType
        split
        · rename_i m' e' shape'
          rw [innerType] at shape'
          simp only [Ty.instantiate, Ty.specification.injEq] at shape'
          obtain ⟨rfl, rfl⟩ := shape'
          exact ⟨_, rfl, rfl, innerUses⟩
        · rename_i other
          exact (other _ _ (by rw [innerType]; rfl)).elim
      | project target =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨inner, innerTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i specType targetType shape
        cases h
        obtain ⟨inner', innerTyped', innerType, innerUses⟩ := ih _ _ _ _ _ innerTyped
        simp only [infer, Option.bind_eq_bind, innerTyped', Option.bind_some]
        rw [shape] at innerType
        split
        · rename_i s' t' shape'
          rw [innerType] at shape'
          simp only [Ty.instantiate, Ty.prototype.injEq] at shape'
          obtain ⟨rfl, rfl⟩ := shape'
          exact ⟨_, rfl, rfl, innerUses⟩
        · rename_i other
          exact (other _ _ (by rw [innerType]; rfl)).elim
      | mix lower upper =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨first, firstTyped, second, secondTyped, h⟩ := h
        obtain ⟨first', firstTyped', firstType, firstUses⟩ := ih _ _ _ _ _ firstTyped
        obtain ⟨second', secondTyped', secondType, secondUses⟩ := ih _ _ _ _ _ secondTyped
        simp only [infer, Option.bind_eq_bind, firstTyped', secondTyped', Option.bind_some]
        split at h
        rotate_left; · cases h
        rename_i self inherited middle self₂ middle₂ provided shapeFirst shapeSecond
        split at h
        rotate_left; · cases h
        rename_i sameSelf
        split at h
        rotate_left; · cases h
        rename_i sameMiddle
        split at h
        rotate_left; · cases h
        rename_i captures
        split at h
        rotate_left; · cases h
        rename_i shareSelf
        split at h
        rotate_left; · cases h
        rename_i shareInherited
        split at h
        rotate_left; · cases h
        rename_i shareMiddle
        cases h
        subst sameSelf sameMiddle
        have s1 := callable_instantiate (σ := σ) shapeFirst
        have s2 := callable_instantiate (σ := σ) shapeSecond
        rw [← firstType] at s1
        rw [← secondType] at s2
        simp only [Ty.instantiate] at s1 s2
        split
        · rename_i a b c a' c' d t1 t2
          rw [s1] at t1
          rw [s2] at t2
          simp only [Ty.arrow.injEq, true_and] at t1 t2
          obtain ⟨rfl, rfl, rfl⟩ := t1
          obtain ⟨rfl, rfl, rfl⟩ := t2
          have c1 : reusableCaptures instance_.shareableVariables (instantiateContext σ context)
              (addUses first'.uses second'.uses) = true := by
            rw [firstUses, secondUses, reusableCaptures_instantiate D.shareable]; exact captures
          rw [dif_pos rfl, dif_pos rfl, dif_pos c1, dif_pos (by rw [shareableUnder_instantiate D.shareable]; exact shareSelf),
            dif_pos (by rw [shareableUnder_instantiate D.shareable]; exact shareInherited),
            dif_pos (by rw [shareableUnder_instantiate D.shareable]; exact shareMiddle)]
          exact ⟨_, rfl, rfl, by dsimp only; rw [firstUses, secondUses]⟩
        · rename_i other
          exact (other _ _ _ _ _ _ s1 s2).elim
      | fix spec inheritedTerm =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨code, codeTyped, base, baseTyped, h⟩ := h
        obtain ⟨code', codeTyped', codeType, codeUses⟩ := ih _ _ _ _ _ codeTyped
        obtain ⟨base', baseTyped', baseType, baseUses⟩ := ih _ _ _ _ _ baseTyped
        simp only [infer, Option.bind_eq_bind, codeTyped', baseTyped', Option.bind_some]
        split at h
        rotate_left; · cases h
        rename_i target inherited output shape
        split at h
        rotate_left; · cases h
        rename_i sameOutput
        split at h
        rotate_left; · cases h
        rename_i agreed
        split at h
        rotate_left; · cases h
        rename_i shareTarget
        split at h
        rotate_left; · cases h
        rename_i allowed
        split at h
        rotate_left; · cases h
        rename_i captures
        cases h
        subst sameOutput
        have s1 := callable_instantiate (σ := σ) shape
        rw [← codeType] at s1
        simp only [Ty.instantiate] at s1
        split
        · rename_i a b c t1
          rw [s1] at t1
          simp only [Ty.arrow.injEq, true_and] at t1
          obtain ⟨rfl, rfl, rfl⟩ := t1
          have a1 : agree instance_ base'.type (inherited.instantiate σ) = true := by
            rw [baseType]; exact D.agree_instantiate agreed
          have a2 : argumentAllowed instance_ .unrestricted (instantiateContext σ context) (inherited.instantiate σ)
              base'.uses = true := by
            rw [baseUses, D.argumentAllowed_instantiate]; exact allowed
          have a3 : reusableCaptures instance_.shareableVariables (instantiateContext σ context) code'.uses = true := by
            rw [codeUses, reusableCaptures_instantiate D.shareable]; exact captures
          rw [dif_pos rfl, dif_pos a1, dif_pos (by rw [shareableUnder_instantiate D.shareable]; exact shareTarget),
            dif_pos a2, dif_pos a3]
          exact ⟨_, rfl, rfl, by dsimp only; rw [codeUses, baseUses]⟩
        · rename_i other
          exact (other _ _ _ s1).elim
      | binary primitive left right =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨l, lTyped, r, rTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i lShape
        split at h
        rotate_left; · cases h
        rename_i rShape
        cases h
        obtain ⟨l', lTyped', lType, lUses⟩ := ih _ _ _ _ _ lTyped
        obtain ⟨r', rTyped', rType, rUses⟩ := ih _ _ _ _ _ rTyped
        have prim := primitiveTypes_instantiate (σ := σ) primitive
        have l1 : l'.type = (primitiveTypes primitive).1 := by rw [lType, lShape, prim.1]
        have r1 : r'.type = (primitiveTypes primitive).1 := by rw [rType, rShape, prim.1]
        simp only [infer, Option.bind_eq_bind, lTyped', rTyped', Option.bind_some, dif_pos l1, dif_pos r1]
        exact ⟨_, rfl, prim.2.symm, by dsimp only; rw [lUses, rUses]⟩
      | ifZero value zero successor =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨c, cTyped, z, zTyped, s, sTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i cShape
        split at h
        rotate_left; · cases h
        rename_i same
        split at h
        rotate_left; · cases h
        rename_i safe
        cases h
        obtain ⟨c', cTyped', cType, cUses⟩ := ih _ _ _ _ _ cTyped
        obtain ⟨z', zTyped', zType, zUses⟩ := ih _ _ _ _ _ zTyped
        obtain ⟨s', sTyped', sType, sUses⟩ := ih _ _ _ _ _ sTyped
        simp only [instantiateContext_cons, Ty.instantiate] at sTyped'
        have c1 : c'.type = .natural := by rw [cType, cShape]; rfl
        have s1 : s'.type = z'.type := by rw [sType, zType, same]
        have u1 : safeUses (⟨.natural, .unrestricted⟩ :: instantiateContext σ context) s'.uses = true := by
          rw [sUses, show (⟨.natural, .unrestricted⟩ :: instantiateContext σ context : Context) =
            instantiateContext σ (⟨.natural, .unrestricted⟩ :: context) from rfl, safeUses_instantiate]; exact safe
        simp only [infer, Option.bind_eq_bind, cTyped', zTyped', sTyped', Option.bind_some, dif_pos c1, dif_pos s1,
          dif_pos u1]
        exact ⟨_, rfl, zType, by dsimp only; rw [cUses, zUses, sUses]⟩
      | inject tag payload =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨annotation, found, value, valueTyped, h⟩ := h
        obtain ⟨value', valueTyped', valueType, valueUses⟩ := ih _ _ _ _ _ valueTyped
        have found' : instantiateAnnotations σ annotations position = some (instantiateAnnotation σ annotation) := by
          simp [instantiateAnnotations, found]
        simp only [infer, Option.bind_eq_bind, found', valueTyped', Option.bind_some]
        split at h
        rotate_left; · cases h
        rename_i kind
        rw [dif_pos (show (instantiateAnnotation σ annotation).parameter = .unrestricted ∧
          (instantiateAnnotation σ annotation).reuse = .reusable from kind)]
        split at h
        · rename_i row codomainShape
          split at h
          rotate_left; · cases h
          rename_i member
          split at h
          rotate_left; · cases h
          rename_i agreed
          split at h
          rotate_left; · cases h
          rename_i pure
          cases h
          have shape' : (instantiateAnnotation σ annotation).codomain = .variant (row.instantiate σ) := by
            simp [instantiateAnnotation, codomainShape, Ty.instantiate]
          simp only [shape']
          have m1 : (row.instantiate σ).lookup instance_.bounds (fuel + extra + 1) tag =
              some (instantiateAnnotation σ annotation).domain := by
            rw [show fuel + extra + 1 = fuel + 1 + extra by omega]
            exact D.lookup_instantiate _ _ _ _ member
          have a1 : agree instance_ value'.type (instantiateAnnotation σ annotation).domain = true := by
            rw [valueType]; exact D.agree_instantiate agreed
          have p1 : (instantiateAnnotation σ annotation).domain.isComputation = false := by
            simp only [instantiateAnnotation]; rw [instantiate_isComputation D.pure]; exact pure
          rw [dif_pos m1, dif_pos a1, dif_pos p1]
          exact ⟨_, rfl, rfl, valueUses⟩
        · rename_i index codomainShape
          split at h
          rotate_left; · cases h
          rename_i row aliased
          split at h
          rotate_left; · cases h
          rename_i member
          split at h
          rotate_left; · cases h
          rename_i agreed
          split at h
          rotate_left; · cases h
          rename_i pure
          split at h
          rotate_left; · cases h
          rename_i conversion
          cases h
          have rigid := alias_not_rigid aliased
          have closed := D.closed index _ rigid (Assumptions.alias_bound aliased)
          simp only [Ty.instantiate, Ty.variant.injEq] at closed
          have shape' : (instantiateAnnotation σ annotation).codomain = .variable index := by
            simp [instantiateAnnotation, codomainShape, Ty.instantiate, D.fixed index rigid]
          simp only [shape', D.aliases index rigid, aliased]
          have m1 : row.lookup instance_.bounds (fuel + extra + 1) tag =
              some (instantiateAnnotation σ annotation).domain := by
            rw [show fuel + extra + 1 = fuel + 1 + extra by omega]
            have := D.lookup_instantiate _ _ _ _ member
            rwa [closed] at this
          have a1 : agree instance_ value'.type (instantiateAnnotation σ annotation).domain = true := by
            rw [valueType]; exact D.agree_instantiate agreed
          have p1 : (instantiateAnnotation σ annotation).domain.isComputation = false := by
            simp only [instantiateAnnotation]; rw [instantiate_isComputation D.pure]; exact pure
          have c1 : sameType instance_ (.variant row) (.variable index) = true := by
            have := D.sameType_instantiate conversion
            simpa [Ty.instantiate, closed, D.fixed index rigid] using this
          rw [dif_pos m1, dif_pos a1, dif_pos p1, dif_pos c1]
          exact ⟨_, rfl, by simp [Ty.instantiate, D.fixed index rigid], valueUses⟩
        · cases h
      | case scrutinee arms =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨value, valueTyped, h⟩ := h
        obtain ⟨value', valueTyped', valueType, valueUses⟩ := ih _ _ _ _ _ valueTyped
        simp only [infer, Option.bind_eq_bind, valueTyped', Option.bind_some]
        split at h
        · rename_i plan response produced activity
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨row, rowFound, typed, armsTyped, h⟩ := h
          split at h
          rotate_left; · cases h
          rename_i planType responseType result resultShape
          split at h
          rotate_left; · cases h
          rename_i agreed
          split at h
          rotate_left; · cases h
          rename_i pureResult
          cases h
          have activity' : value'.type = .computation (plan.instantiate σ) (response.instantiate σ)
              (produced.instantiate σ) := by rw [valueType, activity]; rfl
          obtain ⟨typed', armsTyped', typedRow, typedResult, typedUses⟩ := ihArms _ _ _ _ _ _ _ _ armsTyped
          simp only [Option.map_none] at armsTyped'
          rw [resultShape] at typedResult
          split
          · rename_i a b c activity''
            rw [activity'] at activity''
            simp only [Ty.computation.injEq] at activity''
            obtain ⟨rfl, rfl, rfl⟩ := activity''
            simp only [D.variantRow_instantiate rowFound, Option.bind_some, armsTyped']
            split
            · rename_i p' r' res' resultShape'
              rw [typedResult] at resultShape'
              simp only [Ty.instantiate, Ty.computation.injEq] at resultShape'
              obtain ⟨rfl, rfl, rfl⟩ := resultShape'
              have a1 : agree instance_ value'.type
                  (.computation (planType.instantiate σ) (responseType.instantiate σ) (.variant typed'.row)) = true := by
                rw [typedRow, valueType]; exact D.agree_instantiate agreed
              have p1 : (result.instantiate σ).isComputation = false := by
                rw [instantiate_isComputation D.pure]; exact pureResult
              rw [dif_pos a1, dif_pos p1]
              exact ⟨_, rfl, rfl, by dsimp only; rw [valueUses, typedUses]⟩
            · rename_i other
              exact (other _ _ _ typedResult).elim
          · rename_i other
            exact (other _ _ _ activity').elim
        · rename_i notActivity
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨row, rowFound, typed, armsTyped, h⟩ := h
          split at h
          rotate_left; · cases h
          rename_i agreed
          cases h
          obtain ⟨typed', armsTyped', typedRow, typedResult, typedUses⟩ := ihArms _ _ _ _ _ _ _ _ armsTyped
          simp only [Option.map_none] at armsTyped'
          have pureValue : value.type.isComputation = false := by
            cases shape : value.type with
            | computation p r a => exact (notActivity p r a shape).elim
            | _ => rfl
          split
          · rename_i p r a activity
            have := instantiate_isComputation D.pure value.type
            rw [← valueType, activity, pureValue] at this
            cases this
          · have vr : variantRow instance_ value'.type = some (row.instantiate σ) := by
              rw [valueType]; exact D.variantRow_instantiate rowFound
            simp only [vr, Option.bind_some, armsTyped']
            have a1 : agree instance_ value'.type (.variant typed'.row) = true := by
              rw [typedRow, valueType]
              exact D.agree_instantiate agreed
            rw [dif_pos a1]
            exact ⟨_, rfl, typedResult, by dsimp only; rw [valueUses, typedUses]⟩
      | ifBool condition whenTrue whenFalse =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨c, cTyped, t, tTyped, f, fTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i cShape
        split at h
        rotate_left; · cases h
        rename_i same
        cases h
        obtain ⟨c', cTyped', cType, cUses⟩ := ih _ _ _ _ _ cTyped
        obtain ⟨t', tTyped', tType, tUses⟩ := ih _ _ _ _ _ tTyped
        obtain ⟨f', fTyped', fType, fUses⟩ := ih _ _ _ _ _ fTyped
        have c1 : c'.type = .boolean := by rw [cType, cShape]; rfl
        have s1 : f'.type = t'.type := by rw [fType, tType, same]
        simp only [infer, Option.bind_eq_bind, cTyped', tTyped', fTyped', Option.bind_some, dif_pos c1, dif_pos s1]
        exact ⟨_, rfl, tType, by dsimp only; rw [cUses, tUses, fUses]⟩
      | perform plan =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨annotation, found, value, valueTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i agreed
        split at h
        rotate_left; · cases h
        rename_i isPlan
        split at h
        rotate_left; · cases h
        rename_i isData
        cases h
        obtain ⟨value', valueTyped', valueType, valueUses⟩ := ih _ _ _ _ _ valueTyped
        have found' : instantiateAnnotations σ annotations position = some (instantiateAnnotation σ annotation) := by
          simp [instantiateAnnotations, found]
        have dom : annotation.domain.instantiate σ = annotation.domain := isPlan_instantiate isPlan
        have cod : annotation.codomain.instantiate σ = annotation.codomain := instantiate_of_isData isData
        simp only [infer, Option.bind_eq_bind, found', valueTyped', Option.bind_some, instantiateAnnotation, dom, cod]
        have a1 : agree instance_ value'.type annotation.domain = true := by
          rw [valueType, ← dom]; exact D.agree_instantiate agreed
        rw [dif_pos a1, dif_pos isPlan, dif_pos isData]
        exact ⟨_, rfl, by simp [Ty.instantiate, dom, cod], valueUses⟩
      | done inner =>
        simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨annotation, found, value, valueTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i pureValue
        cases h
        obtain ⟨value', valueTyped', valueType, valueUses⟩ := ih _ _ _ _ _ valueTyped
        have found' : instantiateAnnotations σ annotations position = some (instantiateAnnotation σ annotation) := by
          simp [instantiateAnnotations, found]
        have p1 : value'.type.isComputation = false := by
          rw [valueType, instantiate_isComputation D.pure]; exact pureValue
        simp only [infer, Option.bind_eq_bind, found', valueTyped', Option.bind_some, dif_pos p1]
        exact ⟨_, rfl, by simp [Ty.instantiate, instantiateAnnotation, valueType], valueUses⟩
    · intro annotations context position index fields result h
      cases fields with
      | nil =>
        simp only [inferFields] at h; cases h
        exact ⟨_, rfl, rfl, zeroUses_instantiate context⟩
      | cons head rest =>
        obtain ⟨name, body⟩ := head
        simp only [inferFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨first, firstTyped, later, laterTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i pureFirst
        cases h
        obtain ⟨first', firstTyped', firstType, firstUses⟩ := ih _ _ _ _ _ firstTyped
        obtain ⟨later', laterTyped', laterType, laterUses⟩ := ihFields _ _ _ _ _ _ laterTyped
        have p1 : first'.type.isComputation = false := by
          rw [firstType, instantiate_isComputation D.pure]; exact pureFirst
        simp only [inferFields, Option.bind_eq_bind, firstTyped', laterTyped', Option.bind_some, dif_pos p1]
        exact ⟨_, rfl, by simp [Ty.instantiate, firstType, laterType], by dsimp only; rw [firstUses, laterUses]⟩
    · intro annotations context position index row expected arms result h
      cases arms with
      | nil =>
        cases expected with
        | none => simp [inferArms] at h
        | some result =>
          simp only [inferArms] at h; cases h
          exact ⟨_, rfl, rfl, rfl, zeroUses_instantiate context⟩
      | cons head rest =>
        obtain ⟨name, body⟩ := head
        simp only [inferArms, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨payload, found, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i sharePayload
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨first, firstTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i safe
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨later, laterTyped, h⟩ := h
        split at h
        rotate_left; · cases h
        rename_i same
        cases h
        have found' : (row.instantiate σ).lookup instance_.bounds (fuel + extra + 1) name = some (payload.instantiate σ) := by
          rw [show fuel + extra + 1 = fuel + 1 + extra by omega]
          exact D.lookup_instantiate _ _ _ _ found
        have s1 : (payload.instantiate σ).shareableUnder instance_.shareableVariables = true := by
          rw [shareableUnder_instantiate D.shareable]; exact sharePayload
        obtain ⟨first', firstTyped', firstType, firstUses⟩ := ih _ _ _ _ _ firstTyped
        simp only [instantiateContext_cons] at firstTyped'
        obtain ⟨later', laterTyped', laterRow, laterResult, laterUses⟩ := ihArms _ _ _ _ _ _ _ _ laterTyped
        simp only [Option.map_some] at laterTyped'
        rw [← firstType] at laterTyped'
        have u1 : safeUses (⟨payload.instantiate σ, .unrestricted⟩ :: instantiateContext σ context) first'.uses = true := by
          rw [firstUses, ← instantiateContext_cons, safeUses_instantiate]; exact safe
        have l1 : later'.result = first'.type := by rw [laterResult, firstType, same]
        simp only [inferArms, Option.bind_eq_bind, found', Option.bind_some, dif_pos s1, firstTyped', dif_pos u1,
          laterTyped', dif_pos l1]
        exact ⟨_, rfl, by simp [Ty.instantiate, laterRow], firstType, by dsimp only; rw [firstUses, laterUses]⟩


end

/-- The checker-level statement: a template `check` accepted under rigid bounds is accepted
at every discharging instance (the instance's own premises must be valid, as for any program). -/
theorem Discharges.check_instantiate {σ : Nat → Ty} {instance_ : Assumptions} {extra : Nat} {source : AnnotatedTerm} {context : Context} {fuel : Nat}
    {checked : Checked source context} (D : Discharges σ source.assumptions instance_ extra)
    (accepted : check source context fuel = some checked) (valid : instance_.valid = true) :
    ∃ checked' : Checked ⟨source.term, instantiateAnnotations σ source.annotations, instance_⟩
        (instantiateContext σ context),
      check ⟨source.term, instantiateAnnotations σ source.annotations, instance_⟩ (instantiateContext σ context)
          (fuel + extra) = some checked' ∧
        checked'.type = checked.type.instantiate σ := by
  simp only [check, Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨result, inferred, accepted⟩ := accepted
  split at accepted
  rotate_left; · cases accepted
  rename_i safe
  split at accepted
  rotate_left; · cases accepted
  rename_i contextValid
  split at accepted
  rotate_left; · cases accepted
  cases accepted
  obtain ⟨result', inferred', resultType, resultUses⟩ := (D.infer_instantiate fuel).1 _ _ _ _ _ inferred
  have s1 : safeUses (instantiateContext σ context) result'.uses = true := by
    rw [resultUses, safeUses_instantiate]; exact safe
  have v1 : validContext instance_.shareableVariables (instantiateContext σ context) = true := by
    rw [validContext_instantiate D.shareable]; exact contextValid
  simp only [check, AnnotatedTerm.erase, Option.bind_eq_bind]
  simp only [inferred', Option.bind_some]
  rw [dif_pos s1, dif_pos v1, dif_pos valid]
  exact ⟨_, rfl, resultType⟩

/-! ### Inhabitants and teeth

A one-method template over a rigid `Self` (index 5) bounded by `{weight: Nat}`: it reads
`self.weight`. Its instance at `{colour: Label, weight: Nat}` (wider, and `weight` one field
deeper than in the bound, so `extra = 1`) discharges the bounds, so `check_instantiate`
accepts it without re-checking. The tooth: a template that returns `self` where the bound
ROW is declared is accepted by the alias checker and refused by the rigid one. -/

def weightBound : Ty := .field "weight" .natural .emptyRow
def colouredRow : Ty := .field "colour" .label (.field "weight" .natural .emptyRow)
def templateAssumptions : Assumptions := ⟨[(5, weightBound)], [5], [5]⟩
def colouredSelf : Nat → Ty := fun j => if j = 5 then colouredRow else .variable j

def weightTemplate : AnnotatedTerm :=
  ⟨.lam (.get (.bound 0) "weight"),
    fun position => if position = [] then some ⟨.variable 5, .natural, .unrestricted, .reusable⟩ else none,
    templateAssumptions⟩

theorem weight_template_accepted : (check weightTemplate [] 8).isSome = true := by decide

theorem coloured_discharges : Discharges colouredSelf templateAssumptions {} 1 where
  fixed j rigid := by
    have : j ≠ 5 := fun e => rigid (by simp [templateAssumptions, e])
    simp [colouredSelf, this]
  bounds j rigid := by
    have : (j == 5) = false := by simpa using fun e => rigid (by simp [templateAssumptions, e])
    simp [templateAssumptions, List.lookup, this]
  aliases j rigid := by
    have hb : (j == 5) = false := by simpa using fun e => rigid (by simp [templateAssumptions, e])
    have hn : j ≠ 5 := by simpa using hb
    simp [Assumptions.alias, templateAssumptions, List.lookup, hb, hn]
  closed j bound rigid found := by
    have : (j == 5) = false := by simpa using fun e => rigid (by simp [templateAssumptions, e])
    simp [templateAssumptions, List.lookup, this] at found
  lookup k bound rigid found fuel name member h := by
    have hk : k = 5 := by simpa [templateAssumptions] using rigid
    subst hk
    simp [templateAssumptions, List.lookup] at found
    subst found
    cases fuel with
    | zero => simp [Ty.lookup] at h
    | succ f =>
      simp only [weightBound, Ty.lookup] at h
      split at h
      · rename_i e; subst e; cases h
        simp [colouredSelf, colouredRow, Ty.lookup, Ty.instantiate]
      · cases f <;> simp [Ty.lookup] at h
  row k bound rigid found fuel h := by
    have hk : k = 5 := by simpa [templateAssumptions] using rigid
    subst hk
    simp [templateAssumptions, List.lookup] at found
    subst found
    cases fuel with
    | zero => simp [Ty.isRow] at h
    | succ f =>
      cases f with
      | zero => simp [weightBound, Ty.isRow] at h
      | succ f => simp [colouredSelf, colouredRow, Ty.isRow]
  shareable j := by
    by_cases e : j = 5
    · subst e; simp [colouredSelf, colouredRow, Ty.shareableUnder, Ty.shareable, templateAssumptions]
    · simp [colouredSelf, e, Ty.shareableUnder, Ty.shareable, templateAssumptions]
  pure j := by
    by_cases e : j = 5
    · subst e; simp [colouredSelf, colouredRow, Ty.isComputation]
    · simp [colouredSelf, e, Ty.isComputation]

/-- The instance at the wider row is accepted BY THE THEOREM, at the instantiated type. -/
theorem coloured_instance_accepted :
    ∃ checked : Checked ⟨weightTemplate.term, instantiateAnnotations colouredSelf weightTemplate.annotations, {}⟩ [],
      check ⟨weightTemplate.term, instantiateAnnotations colouredSelf weightTemplate.annotations, {}⟩ [] 9 =
          some checked ∧
        checked.type = .arrow .reusable .unrestricted colouredRow .natural := by
  obtain ⟨checked, accepted⟩ := Option.isSome_iff_exists.mp weight_template_accepted
  obtain ⟨checked', accepted', type⟩ :=
    Discharges.check_instantiate (instance_ := {}) (context := []) coloured_discharges accepted (by decide)
  refine ⟨checked', accepted', ?_⟩
  rw [type]
  have : checked.type = .arrow .reusable .unrestricted (.variable 5) .natural := by
    have typed : (check weightTemplate [] 8).map Checked.type =
        some (.arrow .reusable .unrestricted (.variable 5) .natural) := by decide
    rw [accepted] at typed
    simpa using typed
  simp [this, Ty.instantiate, colouredSelf]

/-- D2's tooth: `self` returned where the bound row is declared. The alias checker (the
emitted program's) accepts it; the rigid checker (the template's) refuses it. -/
def selfAsBoundRow (rigid : List Nat) : AnnotatedTerm :=
  ⟨.lam (.bound 0),
    fun position => if position = [] then some ⟨.variable 5, weightBound, .unrestricted, .reusable⟩ else none,
    ⟨[(5, weightBound)], [5], rigid⟩⟩

theorem self_as_bound_row_alias_accepted : (check (selfAsBoundRow []) [] 8).isSome = true := by decide
theorem self_as_bound_row_rigid_refused : (check (selfAsBoundRow [5]) [] 8).isNone = true := by decide

#assert_axioms Discharges.lookup_instantiate Discharges.isRow_instantiate Discharges.sameType_instantiate
  Discharges.agree_instantiate Discharges.variantRow_instantiate Discharges.infer_instantiate
  Discharges.check_instantiate weight_template_accepted coloured_discharges coloured_instance_accepted
  self_as_bound_row_alias_accepted self_as_bound_row_rigid_refused
end Minidregg.Theory.ObjectiveBendTemplates

