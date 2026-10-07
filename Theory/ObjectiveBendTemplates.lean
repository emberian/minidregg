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
    obtain ⟨ih, ihFields, ihArms⟩ := by sorry


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
def colouredRow : Ty := sorry
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

-- STUBBED #assert_axioms Discharges.lookup_instantiate Discharges.isRow_instantiate Discharges.sameType_instantiate
  Discharges.agree_instantiate Discharges.variantRow_instantiate Discharges.infer_instantiate
  Discharges.check_instantiate weight_template_accepted coloured_discharges coloured_instance_accepted
  self_as_bound_row_alias_accepted self_as_bound_row_rigid_refused
end Minidregg.Theory.ObjectiveBendTemplates

