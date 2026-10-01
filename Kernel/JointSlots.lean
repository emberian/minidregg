/- Joint participant slots of a declared resource invocation, keyed twice.

`joint/target/{id}/…` names a participant by its cell id; `joint/index/{i}/…`
names the SAME participant by its 0-based position in `command.targets`. A law
written against positions ("the room I leave is target 1") works for every
command of that shape, whatever cells fill the positions. Both keyings are one
function of the same per-participant slot list, so they cannot drift. An index
at or beyond the command's target count names nothing: every Pred atom is false
on an absent slot, so a law that asserts a fact about position `i` refuses a
command without it. A `not` around such an atom is TRUE on absence; a clause of
the form `any [not (… joint/index/i …), …]` is vacuous on a short command unless
another clause requires position `i`. -/
import Kernel.ResourceTransaction
import Compiler.ResourceAuthorityProjection

namespace Minidregg.Kernel.DeclaredResourceController
open Minidregg.Compiler
open Minidregg.Pred
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

def jointTargetKey (target : Nat) (slot : String) : String :=
  "joint/target/" ++ toString target ++ "/" ++ slot

def jointIndexKey (index : Nat) (slot : String) : String :=
  "joint/index/" ++ toString index ++ "/" ++ slot

/-- `slots i` is participant `i`'s own projection (the names a law on that
participant would read locally). Every one of them is exposed under both keys. -/
def jointSlots (targets : List Target) (slots : Fin targets.length → List (String × Int)) :
    List (String × Int) :=
  (List.finRange targets.length).flatMap (fun i =>
      (slots i).map fun slot => (jointTargetKey targets[i].target slot.1, slot.2)) ++
    (List.finRange targets.length).flatMap (fun i =>
      (slots i).map fun slot => (jointIndexKey i.val slot.1, slot.2))

namespace JointSlots

theorem get_append (k : String) (xs ys : List (String × Int)) :
    State.get ⟨xs ++ ys⟩ k = (State.get ⟨xs⟩ k).or (State.get ⟨ys⟩ k) := by
  unfold State.get; rw [List.find?_append]; cases List.find? (fun p => p.1 == k) xs <;> simp

theorem get_none (k : String) (xs : List (String × Int)) (h : ∀ p ∈ xs, p.1 ≠ k) :
    State.get ⟨xs⟩ k = none := by
  unfold State.get; simp only [Option.map_eq_none_iff, List.find?_eq_none]
  intro p hp; simpa using h p hp

private theorem slash_split : ∀ (a b xs ys : List Char), (∀ c ∈ a, c ≠ '/') → (∀ c ∈ b, c ≠ '/') →
    a ++ '/' :: xs = b ++ '/' :: ys → a = b ∧ xs = ys
  | [], [], _, _, _, _, h => by simpa using h
  | [], c :: b, _, _, _, hb, h => by
      simp at h; exact absurd h.1.symm (hb c (by simp))
  | c :: a, [], _, _, ha, _, h => by
      simp at h; exact absurd h.1 (ha c (by simp))
  | c :: a, d :: b, xs, ys, ha, hb, h => by
      simp only [List.cons_append, List.cons.injEq] at h
      have := slash_split a b xs ys (fun x hx => ha x (by simp [hx])) (fun x hx => hb x (by simp [hx])) h.2
      exact ⟨by rw [h.1, this.1], this.2⟩

private theorem digits_no_slash (n : Nat) : ∀ c ∈ Nat.toDigits 10 n, c ≠ '/' := by
  intro c hc h
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  subst h; exact absurd this (by decide)

/-- A decimal number terminated by `/` is uniquely parsed back out of a key. -/
theorem numbered_key_injective (stem : String) (m n : Nat) (s t : String)
    (h : stem ++ toString m ++ "/" ++ s = stem ++ toString n ++ "/" ++ t) : m = n ∧ s = t := by
  have h' := congrArg String.toList h
  simp only [String.toList_append, List.append_assoc] at h'
  have h'' := List.append_cancel_left h'
  simp only [Nat.toString_eq_repr, Nat.toList_repr] at h''
  have := slash_split _ _ _ _ (digits_no_slash m) (digits_no_slash n) (by simpa using h'')
  refine ⟨?_, String.toList_inj.mp this.2⟩
  have := congrArg (fun l => Nat.ofDigitChars 10 l 0) this.1
  simpa using this

theorem jointTargetKey_injective (m n : Nat) (s t : String)
    (h : jointTargetKey m s = jointTargetKey n t) : m = n ∧ s = t :=
  numbered_key_injective _ m n s t h

theorem jointIndexKey_injective (m n : Nat) (s t : String)
    (h : jointIndexKey m s = jointIndexKey n t) : m = n ∧ s = t :=
  numbered_key_injective _ m n s t h

theorem jointTargetKey_ne_jointIndexKey (m n : Nat) (s t : String) :
    jointTargetKey m s ≠ jointIndexKey n t := by
  intro h
  have h' := congrArg String.toList h
  have lt : "joint/target/".toList = ['j', 'o', 'i', 'n', 't', '/', 't', 'a', 'r', 'g', 'e', 't', '/'] := by decide
  have li : "joint/index/".toList = ['j', 'o', 'i', 'n', 't', '/', 'i', 'n', 'd', 'e', 'x', '/'] := by decide
  simp [jointTargetKey, jointIndexKey, String.toList_append, lt, li] at h'

/-- The first character of a key; every joint key begins with `j`. -/
def Unjoint (xs : List (String × Int)) : Prop := ∀ p ∈ xs, p.1.toList.head? ≠ some 'j'

theorem head_append (stem rest : String) (c : Char) (h : stem.toList.head? = some c) :
    (stem ++ rest).toList.head? = some c := by
  simp only [String.toList_append]
  cases hs : stem.toList with
  | nil => simp [hs] at h
  | cons d ds => simp [hs] at h ⊢; exact h

theorem jointTargetKey_head (m : Nat) (s : String) : (jointTargetKey m s).toList.head? = some 'j' := by
  unfold jointTargetKey; simp only [String.append_assoc]; exact head_append _ _ _ (by decide)

theorem jointIndexKey_head (m : Nat) (s : String) : (jointIndexKey m s).toList.head? = some 'j' := by
  unfold jointIndexKey; simp only [String.append_assoc]; exact head_append _ _ _ (by decide)

theorem get_unjoint (xs : List (String × Int)) (h : Unjoint xs) (k : String)
    (hk : k.toList.head? = some 'j') : State.get ⟨xs⟩ k = none :=
  get_none k xs fun p hp eq => h p hp (eq ▸ hk)

/-- One participant's block under key family `K` at coordinate `m`. -/
theorem get_block (K : Nat → String → String)
    (hK : ∀ m n s t, K m s = K n t → m = n ∧ s = t) (m n : Nat) (slot : String)
    (xs : List (String × Int)) :
    State.get ⟨xs.map fun p => (K m p.1, p.2)⟩ (K n slot) =
      if m = n then State.get ⟨xs⟩ slot else none := by
  split
  · subst m
    unfold State.get
    rw [List.find?_map, Option.map_map]
    have hp : ((fun p : String × Int => p.1 == K n slot) ∘ fun p : String × Int => (K n p.1, p.2)) =
        fun p : String × Int => p.1 == slot := by
      funext p
      by_cases e : p.1 = slot
      · simp [Function.comp, e]
      · have ne : K n p.1 ≠ K n slot := fun h => e (hK _ _ _ _ h).2
        simp [Function.comp, e, ne]
    rw [hp]
    rfl
  · apply get_none
    intro p hp e
    simp only [List.mem_map] at hp
    obtain ⟨q, _, rfl⟩ := hp
    exact ‹¬m = n› (hK _ _ _ _ e).1

theorem get_blocks_absent {α : Type} (K : Nat → String → String)
    (hK : ∀ m n s t, K m s = K n t → m = n ∧ s = t) (f : α → Nat)
    (S : α → List (String × Int)) (n : Nat) (slot : String) :
    ∀ L : List α, (∀ j ∈ L, f j ≠ n) →
      State.get ⟨L.flatMap fun j => (S j).map fun p => (K (f j) p.1, p.2)⟩ (K n slot) = none
  | [], _ => rfl
  | j :: L, h => by
      rw [List.flatMap_cons, get_append, get_block K hK, if_neg (h j (by simp)),
        get_blocks_absent K hK f S n slot L (fun j' hj => h j' (by simp [hj]))]
      rfl

theorem get_blocks {α : Type} (K : Nat → String → String)
    (hK : ∀ m n s t, K m s = K n t → m = n ∧ s = t) (f : α → Nat)
    (S : α → List (String × Int)) (slot : String) :
    ∀ L : List α, (L.map f).Nodup → ∀ j ∈ L,
      State.get ⟨L.flatMap fun j => (S j).map fun p => (K (f j) p.1, p.2)⟩ (K (f j) slot) =
        State.get ⟨S j⟩ slot
  | [], _, _, hj => by simp at hj
  | j' :: L, nd, j, hj => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at nd
      rw [List.flatMap_cons, get_append, get_block K hK]
      by_cases e : f j' = f j
      · rw [if_pos e]
        have jj : j' = j ∨ j ∈ L := by simpa [eq_comm] using hj
        have rest := get_blocks_absent K hK f S (f j) slot L
          (fun x hx hfx => nd.1 ⟨x, hx, hfx.trans e.symm⟩)
        rw [rest]
        cases jj with
        | inl h => subst h; cases State.get ⟨S j'⟩ slot <;> rfl
        | inr h => exact absurd ⟨j, h, e.symm⟩ nd.1
      · rw [if_neg e]
        have : j ∈ L := by
          rcases List.mem_cons.mp hj with h | h
          · exact absurd (h ▸ rfl) e
          · exact h
        exact get_blocks K hK f S slot L nd.2 j this

/-- Position `i` of the command reads participant `i`'s own slots. -/
theorem jointSlots_index (targets : List Target) (slots : Fin targets.length → List (String × Int))
    (i : Fin targets.length) (slot : String) :
    State.get ⟨jointSlots targets slots⟩ (jointIndexKey i.val slot) = State.get ⟨slots i⟩ slot := by
  unfold jointSlots
  rw [get_append,
    get_none _ _ (fun p hp e => by
      simp only [List.mem_flatMap, List.mem_map] at hp
      obtain ⟨_, _, q, _, rfl⟩ := hp
      exact jointTargetKey_ne_jointIndexKey _ _ _ _ e),
    get_blocks jointIndexKey jointIndexKey_injective Fin.val slots slot _
      ((List.nodup_finRange _).map Fin.val_injective) i (List.mem_finRange i)]
  rfl

/-- A position at or past the command's target count names no slot. -/
theorem jointSlots_index_absent (targets : List Target) (slots : Fin targets.length → List (String × Int))
    (n : Nat) (h : targets.length ≤ n) (slot : String) :
    State.get ⟨jointSlots targets slots⟩ (jointIndexKey n slot) = none := by
  unfold jointSlots
  rw [get_append,
    get_none _ _ (fun p hp e => by
      simp only [List.mem_flatMap, List.mem_map] at hp
      obtain ⟨_, _, q, _, rfl⟩ := hp
      exact jointTargetKey_ne_jointIndexKey _ _ _ _ e),
    get_blocks_absent jointIndexKey jointIndexKey_injective Fin.val slots n slot _
      (fun j _ e => by omega)]
  rfl

/-- Under distinct target ids (`PreparedInvocation.distinct`), the id key of
participant `i` also reads participant `i`'s own slots. -/
theorem jointSlots_target (targets : List Target) (slots : Fin targets.length → List (String × Int))
    (distinct : (targets.map Target.target).Nodup) (i : Fin targets.length) (slot : String) :
    State.get ⟨jointSlots targets slots⟩ (jointTargetKey targets[i].target slot) =
      State.get ⟨slots i⟩ slot := by
  unfold jointSlots
  have nd : ((List.finRange targets.length).map fun j => targets[j].target).Nodup := by
    refine (List.nodup_finRange _).map ?_
    intro a b e
    apply Fin.ext
    apply (List.Nodup.getElem_inj_iff distinct (i := a.val) (j := b.val) (hi := by simp)
      (hj := by simp)).mp
    simpa using e
  have hb := get_blocks (α := Fin targets.length) jointTargetKey jointTargetKey_injective
    (fun j => targets[j].target) slots slot (List.finRange targets.length) nd i (List.mem_finRange i)
  have hn : State.get ⟨(List.finRange targets.length).flatMap fun j =>
      (slots j).map fun p => (jointIndexKey j.val p.1, p.2)⟩ (jointTargetKey targets[i].target slot) = none :=
    get_none _ _ (fun p hp e => by
      simp only [List.mem_flatMap, List.mem_map] at hp
      obtain ⟨_, _, q, _, rfl⟩ := hp
      exact jointTargetKey_ne_jointIndexKey _ _ _ _ e.symm)
  rw [get_append, hb, hn, Option.or_none]

theorem unjoint_append (xs ys : List (String × Int)) (hx : Unjoint xs) (hy : Unjoint ys) :
    Unjoint (xs ++ ys) := by
  intro p hp; rcases List.mem_append.mp hp with h | h
  · exact hx p h
  · exact hy p h

theorem bytesSlots_unjoint (stem : String) (c : Char) (hc : stem.toList.head? = some c) (ne : c ≠ 'j') :
    ∀ (offset : Nat) (bytes : List UInt8), Unjoint (ResourceAuthorityProjection.bytesSlots stem offset bytes)
  | _, [] => by intro p hp; simp [ResourceAuthorityProjection.bytesSlots] at hp
  | offset, byte :: rest => by
      intro p hp
      simp only [ResourceAuthorityProjection.bytesSlots, List.mem_cons] at hp
      rcases hp with rfl | hp
      · have : (s!"{stem}/{offset}").toList.head? = some c := by
          show (stem ++ "/" ++ toString offset).toList.head? = some c
          simp only [String.append_assoc]
          exact head_append _ _ _ hc
        rw [this]; simpa using ne
      · exact bytesSlots_unjoint stem c hc ne (offset + 1) rest p hp

theorem requestSlots_unjoint {kind : ResourceKind} (request : Request kind) :
    Unjoint (CanonicalRuntimeProfile.requestSlots request) := by
  intro p hp
  simp only [CanonicalRuntimeProfile.requestSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide

theorem scalarSlots_unjoint (before after : DeclaredResourceProjection.Values) :
    Unjoint (DeclaredResourceProjection.scalarSlots before after) := by
  have field : ∀ n v, (DeclaredResourceProjection.fieldName n v).toList.head? ≠ some 'j' := by
    intro n v
    show ("resource/field/" ++ toString n ++ "/" ++ v).toList.head? ≠ some 'j'
    simp only [String.append_assoc]
    rw [head_append _ _ 'r' (by decide)]; decide
  have pair : ∀ a b, (DeclaredResourceProjection.pairName a b).toList.head? ≠ some 'j' := by
    intro a b
    show ("resource/pair/" ++ toString a ++ "/" ++ toString b ++ "/delta").toList.head? ≠ some 'j'
    simp only [String.append_assoc]
    rw [head_append _ _ 'r' (by decide)]; decide
  intro p hp
  unfold DeclaredResourceProjection.scalarSlots at hp
  rcases List.mem_append.mp hp with hp | hp
  rcases List.mem_append.mp hp with hp | hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp; exact field _ _
  · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp; exact field _ _
  · obtain ⟨q, _, h⟩ := List.mem_filterMap.mp hp
    obtain ⟨old, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact field _ _
  · obtain ⟨a, _, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨b, _, h⟩ := List.mem_filterMap.mp hp
    cases ha : DeclaredResourceProjection.get before a.1 with
    | none => simp [ha] at h
    | some oldA =>
      cases hb : DeclaredResourceProjection.get before b.1 with
      | none => simp [ha, hb] at h
      | some oldB =>
        simp only [ha, hb, Option.bind_some, Option.some.injEq, bind, pure] at h
        subst h; exact pair _ _

theorem contentProject_unjoint (before after : ContentResource.ContentStore) (command : ContentResource.Command) :
    Unjoint (ContentResource.project before after command) := by
  intro p hp
  simp only [ContentResource.project, List.mem_cons, List.not_mem_nil, or_false] at hp
  -- One case per content slot, however many the projection has (K-CONTENT
  -- added five); every key starts with `content/`.
  repeat' (first | (rcases hp with rfl | hp) | subst hp)
  all_goals (dsimp only; decide)

end JointSlots
end Minidregg.Kernel.DeclaredResourceController
