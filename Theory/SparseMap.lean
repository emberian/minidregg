/-
# Theory.SparseMap -- the leaf representation: a persistent extensional finite map

Retained mode's leaf layer (`docs/RETAINED-MODE.md` §5, L0). A `SparseMap K V` is a finite map
from keys to present values, held as a `Std.ExtDTreeMap` (a balanced tree, persistent by path
copying, extensional: two maps with the same lookups are equal). Every `get?`, `set` (insert or
erase) and `ext` is O(encode k + comparison · log n). It replaces `DFinsupp` as the runtime carrier
of `Theory.Store`'s stores and the World's cell map: a `DFinsupp.update` adds a closure layer per
write, so lookups walked every write since the last re-tree (`Compiler/WorldCompact.lean`'s
header: 99 % of a 175 s open inside `Function.update`). `toDFinsupp` keeps the DFinsupp as a
specification view (`toDFinsupp_apply`).

* `StoreKey α`: an injective code `α → List Nat`. `List Nat` carries a lawful order in Std, so
  every key type with a code is ordered without per-type order proofs. Instances: `Nat`, `Unit`,
  `Bool`, `Fin`, `UInt8`, `Option`, `Prod`, `Sum`, `Sigma` (dependent), `List`, and `ofInjective`.
  Components are framed by their length, never concatenated ambiguously.
* `CachedKey α`: a key with its code computed once; the tree compares cached codes only.
* `SparseMap K V`: `get?`, `set`, `empty`, `ext`, `support`, `toList`, `filter`, `toDFinsupp`,
  `DecidableEq`; `coe_set` says `set` is `Function.update` of the lookup function.

Kernel evaluation: `by decide` reduces lookups, inserts, erases and equality of concrete maps
(the `Example` section), so concrete-store witnesses keep working.
-/
module

public import Std.Data.ExtDTreeMap
public import Mathlib.Data.DFinsupp.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic.Common
import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Theory

set_option autoImplicit false

universe u v w

/-- `none` is the representation-level zero of an optional value: absence, not a default. -/
instance optionZero (α : Type w) : Zero (Option α) := ⟨none⟩

/-! ## Keys -/

/-- An injective code into `List Nat`: the order every map key is compared by. -/
class StoreKey (α : Type u) where
  code : α → List Nat
  injective : Function.Injective code

namespace StoreKey

/-- A framed component: its length, then its digits. -/
def frame (l : List Nat) : List Nat := l.length :: l

theorem frame_append_inj {l₁ l₂ r₁ r₂ : List Nat} (h : frame l₁ ++ r₁ = frame l₂ ++ r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  simp only [frame, List.cons_append, List.cons.injEq] at h
  obtain ⟨len, rest⟩ := h
  exact List.append_inj rest len

/-- Equal codes, equal keys. -/
theorem code_inj {α : Type u} [StoreKey α] {a b : α} : code a = code b ↔ a = b :=
  ⟨fun h => injective h, fun h => h ▸ rfl⟩

/-- Key equality, decided by codes. -/
def decEq (α : Type u) [StoreKey α] : DecidableEq α :=
  fun a b => decidable_of_iff (code a = code b) code_inj

instance nat : StoreKey Nat where
  code n := [n]
  injective _ _ h := by simpa using h

instance unit : StoreKey Unit where
  code _ := []
  injective _ _ _ := rfl

instance bool : StoreKey Bool where
  code b := [if b then 1 else 0]
  injective a b h := by cases a <;> cases b <;> simp_all

instance fin (n : Nat) : StoreKey (Fin n) where
  code i := [i.val]
  injective a b h := Fin.ext (by simpa using h)

instance uint8 : StoreKey UInt8 where
  code b := [b.toNat]
  injective a b h := UInt8.toNat_inj.mp (by simpa using h)

instance option (α : Type u) [StoreKey α] : StoreKey (Option α) where
  code
    | none => [0]
    | some a => 1 :: code a
  injective a b h := by
    cases a <;> cases b <;> simp_all [code_inj]

instance prod (α : Type u) (β : Type v) [StoreKey α] [StoreKey β] : StoreKey (α × β) where
  code p := frame (code p.1) ++ code p.2
  injective p q h := by
    obtain ⟨h₁, h₂⟩ := frame_append_inj h
    exact Prod.ext (injective h₁) (injective h₂)

instance sum (α : Type u) (β : Type v) [StoreKey α] [StoreKey β] : StoreKey (α ⊕ β) where
  code
    | .inl a => 0 :: code a
    | .inr b => 1 :: code b
  injective a b h := by
    cases a <;> cases b <;> simp_all [code_inj]

instance sigma (α : Type u) (β : α → Type v) [StoreKey α] [∀ a, StoreKey (β a)] :
    StoreKey (Σ a, β a) where
  code p := frame (code p.1) ++ code p.2
  injective p q h := by
    obtain ⟨a, x⟩ := p
    obtain ⟨b, y⟩ := q
    obtain ⟨h₁, h₂⟩ := frame_append_inj h
    have ab : a = b := injective h₁
    subst ab
    have xy : x = y := injective h₂
    subst xy
    rfl

/-- A list of keys: every element framed. -/
def listCode {α : Type u} [StoreKey α] : List α → List Nat
  | [] => [0]
  | a :: rest => 1 :: (frame (code a) ++ listCode rest)

theorem listCode_injective {α : Type u} [StoreKey α] : Function.Injective (listCode (α := α)) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ h; cases l₂ <;> simp_all [listCode]
  | cons a rest ih =>
    intro l₂ h
    cases l₂ with
    | nil => simp [listCode] at h
    | cons b rest' =>
      simp only [listCode, List.cons.injEq, true_and] at h
      obtain ⟨h₁, h₂⟩ := frame_append_inj h
      rw [injective h₁, ih h₂]

instance list (α : Type u) [StoreKey α] : StoreKey (List α) where
  code := listCode
  injective := listCode_injective

/-- A key type with an injective map into a coded one. -/
@[instance_reducible] def ofInjective {α : Type u} {β : Type v} [StoreKey β] (f : α → β) (inj : Function.Injective f) :
    StoreKey α where
  code a := code (f a)
  injective _ _ h := inj (injective h)

end StoreKey

/-- A key with its code computed once. -/
structure CachedKey (α : Type u) [StoreKey α] where
  value : α
  code : List Nat
  exact : code = StoreKey.code value

namespace CachedKey

variable {α : Type u} [StoreKey α]

/-- Cache a key's code. -/
@[inline] def of (a : α) : CachedKey α := ⟨a, StoreKey.code a, rfl⟩

@[simp] theorem of_value (a : α) : (of a).value = a := rfl

theorem eq_of_code_eq {k₁ k₂ : CachedKey α} (h : k₁.code = k₂.code) : k₁ = k₂ := by
  obtain ⟨a, c, ea⟩ := k₁
  obtain ⟨b, d, eb⟩ := k₂
  simp only at h
  subst h
  have : a = b := StoreKey.injective (ea.symm.trans eb)
  subst this
  rfl

theorem eq_of (k : CachedKey α) : k = of k.value := eq_of_code_eq k.exact

/-- Cached keys compare by their codes only. -/
abbrev cmp : CachedKey α → CachedKey α → Ordering := compareOn CachedKey.code

instance : Std.LawfulEqCmp (cmp (α := α)) where
  compare_self := by
    intro a
    exact Std.ReflCmp.compare_self (cmp := (compare : List Nat → List Nat → Ordering))
  eq_of_compare := by
    intro a b h
    exact eq_of_code_eq (Std.LawfulEqCmp.eq_of_compare (cmp := (compare : List Nat → List Nat → Ordering)) h)

end CachedKey

/-! ## The map -/

/-- A finite map to present values, held as a persistent extensional balanced tree. -/
structure SparseMap (K : Type u) [StoreKey K] (V : K → Type v) where
  tree : Std.ExtDTreeMap (CachedKey K) (fun k => V k.value) CachedKey.cmp

namespace SparseMap

variable {K : Type u} [StoreKey K] {V : K → Type v}

/-- The empty map. -/
def empty : SparseMap K V := ⟨∅⟩

instance : EmptyCollection (SparseMap K V) := ⟨empty⟩

/-- The empty map is the zero (the stores' `0`). -/
instance : Zero (SparseMap K V) := ⟨empty⟩

/-- The value at a key, if present. -/
@[inline] def get? (m : SparseMap K V) (a : K) : Option (V a) := m.tree.get? (CachedKey.of a)

instance : CoeFun (SparseMap K V) (fun _ => (a : K) → Option (V a)) := ⟨get?⟩

/-- Set one key: `some v` inserts or overwrites, `none` removes. -/
def set (m : SparseMap K V) (a : K) : Option (V a) → SparseMap K V
  | some v => ⟨m.tree.insert (CachedKey.of a) v⟩
  | none => ⟨m.tree.erase (CachedKey.of a)⟩

@[simp] theorem get?_empty (a : K) : (empty : SparseMap K V).get? a = none :=
  Std.ExtDTreeMap.get?_empty

@[simp] theorem emptyc_apply (a : K) : (∅ : SparseMap K V) a = none :=
  Std.ExtDTreeMap.get?_empty

@[simp] theorem coe_apply (m : SparseMap K V) (a : K) : m a = m.get? a := rfl

@[simp] theorem zero_apply (a : K) : (0 : SparseMap K V).get? a = none :=
  Std.ExtDTreeMap.get?_empty

theorem ext_tree {m₁ m₂ : SparseMap K V} (h : m₁.tree = m₂.tree) : m₁ = m₂ := by
  cases m₁; cases m₂; cases h; rfl

/-- **Extensionality**: maps with the same lookups are equal. -/
@[ext] theorem ext {m₁ m₂ : SparseMap K V} (h : ∀ a, m₁ a = m₂ a) : m₁ = m₂ := by
  apply ext_tree
  apply Std.ExtDTreeMap.ext_get?
  intro k
  rw [CachedKey.eq_of k]
  exact h k.value

theorem ext_iff' {m₁ m₂ : SparseMap K V} : m₁ = m₂ ↔ ∀ a, m₁ a = m₂ a :=
  ⟨fun h _ => h ▸ rfl, ext⟩

@[simp] theorem set_eq (m : SparseMap K V) (a : K) (v : Option (V a)) : m.set a v a = v := by
  cases v with
  | some v => exact Std.ExtDTreeMap.get?_insert_self
  | none => exact Std.ExtDTreeMap.get?_erase_self

theorem cmp_of_ne {a b : K} (ne : b ≠ a) :
    CachedKey.cmp (CachedKey.of a) (CachedKey.of b) ≠ .eq := by
  intro h
  exact ne (congrArg CachedKey.value (Std.LawfulEqCmp.eq_of_compare h)).symm

theorem set_ne (m : SparseMap K V) (a : K) (v : Option (V a)) (b : K) (ne : b ≠ a) :
    m.set a v b = m b := by
  cases v with
  | some v =>
    show (m.tree.insert (CachedKey.of a) v).get? (CachedKey.of b) = m.tree.get? (CachedKey.of b)
    exact Std.ExtDTreeMap.get?_insert.trans (dif_neg (cmp_of_ne ne))
  | none =>
    show (m.tree.erase (CachedKey.of a)).get? (CachedKey.of b) = m.tree.get? (CachedKey.of b)
    rw [Std.ExtDTreeMap.get?_erase]
    exact if_neg (cmp_of_ne ne)

theorem set_apply [DecidableEq K] (m : SparseMap K V) (a : K) (v : Option (V a)) (b : K) :
    m.set a v b = if h : b = a then h ▸ v else m b := by
  split
  · rename_i h; subst h; exact set_eq m b v
  · rename_i h; exact set_ne m a v b h

/-- `set` is `Function.update` of the lookup function. -/
theorem coe_set [DecidableEq K] (m : SparseMap K V) (a : K) (v : Option (V a)) :
    ⇑(m.set a v) = Function.update (⇑m) a v := by
  funext b
  by_cases h : b = a
  · subst h; simp
  · rw [Function.update_of_ne h]; exact set_ne m a v b h

@[simp] theorem set_set (m : SparseMap K V) (a : K) (v w : Option (V a)) :
    (m.set a v).set a w = m.set a w := by
  ext b
  by_cases h : b = a
  · subst h; simp
  · rw [set_ne _ _ _ _ h, set_ne _ _ _ _ h, set_ne _ _ _ _ h]

theorem set_self (m : SparseMap K V) (a : K) : m.set a (m a) = m := by
  ext b
  by_cases h : b = a
  · subst h; simp
  · rw [set_ne _ _ _ _ h]

theorem set_comm (m : SparseMap K V) {a b : K} (ne : a ≠ b) (v : Option (V a)) (w : Option (V b)) :
    (m.set a v).set b w = (m.set b w).set a v := by
  ext c
  by_cases ha : c = a
  · subst ha; rw [set_ne _ _ _ _ ne, set_eq, set_eq]
  · by_cases hb : c = b
    · subst hb; rw [set_eq, set_ne _ _ _ _ (Ne.symm ne), set_eq]
    · rw [set_ne _ _ _ _ hb, set_ne _ _ _ _ ha, set_ne _ _ _ _ ha, set_ne _ _ _ _ hb]

/-! ### Enumeration -/

/-- The entries, in code order. -/
def toList (m : SparseMap K V) : List (Σ a, V a) :=
  m.tree.toList.map fun e => ⟨e.1.value, e.2⟩

/-- The present keys, in code order. -/
def keys (m : SparseMap K V) : List K := m.tree.keys.map CachedKey.value

theorem mem_keys (m : SparseMap K V) (a : K) : a ∈ m.keys ↔ (m a).isSome := by
  unfold keys
  constructor
  · rintro h
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
    have := (Std.ExtDTreeMap.mem_keys).mp hk
    rw [Std.ExtDTreeMap.mem_iff_isSome_get?] at this
    rw [CachedKey.eq_of k] at this
    exact this
  · intro h
    refine List.mem_map.mpr ⟨CachedKey.of a, ?_, rfl⟩
    exact Std.ExtDTreeMap.mem_keys.mpr (Std.ExtDTreeMap.mem_iff_isSome_get?.mpr h)

theorem nodup_keys (m : SparseMap K V) : m.keys.Nodup := by
  unfold keys
  refine List.Nodup.map_on ?_ Std.ExtDTreeMap.nodup_keys
  intro k₁ _ k₂ _ h
  rw [CachedKey.eq_of k₁, CachedKey.eq_of k₂, h]

/-- The support: the present keys, as a finset (no dedup: the keys are distinct). -/
def support (m : SparseMap K V) : Finset K := ⟨m.keys, m.nodup_keys⟩

@[simp] theorem mem_support_iff (m : SparseMap K V) (a : K) : a ∈ m.support ↔ m a ≠ none := by
  show a ∈ m.keys ↔ _
  rw [mem_keys, Option.isSome_iff_ne_none]

theorem not_mem_support_iff (m : SparseMap K V) (a : K) : a ∉ m.support ↔ m a = none := by
  simp

theorem mem_toList (m : SparseMap K V) (a : K) (v : V a) : ⟨a, v⟩ ∈ m.toList ↔ m a = some v := by
  unfold toList
  constructor
  · intro h
    obtain ⟨⟨k, w⟩, hk, he⟩ := List.mem_map.mp h
    obtain ⟨k', c, ex⟩ := k
    simp only [Sigma.mk.injEq] at he
    obtain ⟨rfl, hv⟩ := he
    have hv' : w = v := eq_of_heq hv
    subst hv'
    have := Std.ExtDTreeMap.mem_toList_iff_get?_eq_some.mp hk
    subst ex
    exact this
  · intro h
    exact List.mem_map.mpr ⟨⟨CachedKey.of a, v⟩, Std.ExtDTreeMap.mem_toList_iff_get?_eq_some.mpr h, rfl⟩

/-- Keep the entries a predicate accepts. -/
def filter (p : (a : K) → V a → Bool) (m : SparseMap K V) : SparseMap K V :=
  ⟨m.tree.filter fun k v => p k.value v⟩

@[simp] theorem filter_apply (p : (a : K) → V a → Bool) (m : SparseMap K V) (a : K) :
    m.filter p a = (m a).filter (p a) :=
  Std.ExtDTreeMap.get?_filter

/-! ### The specification view -/

/-- The map as a `DFinsupp` of options (absence is `none`, the zero). -/
def toDFinsupp [DecidableEq K] (m : SparseMap K V) : Π₀ a : K, Option (V a) :=
  DFinsupp.mk' (fun a => m a) (Trunc.mk ⟨⟨m.keys, fun a => by
    rcases h : m a with _ | v
    · exact Or.inr rfl
    · exact Or.inl ((mem_keys m a).mpr (by simp [h]))⟩, rfl⟩ |>.map Subtype.val)

@[simp] theorem toDFinsupp_apply [DecidableEq K] (m : SparseMap K V) (a : K) :
    m.toDFinsupp a = m a := rfl

/-- Transport: `set` is `DFinsupp.update` under the specification view. -/
theorem toDFinsupp_set [DecidableEq K] (m : SparseMap K V) (a : K) (v : Option (V a)) :
    (m.set a v).toDFinsupp = m.toDFinsupp.update a v := by
  apply DFinsupp.ext
  intro b
  rw [DFinsupp.coe_update, toDFinsupp_apply]
  have view : (⇑m.toDFinsupp : (a : K) → Option (V a)) = ⇑m := funext (toDFinsupp_apply m)
  rw [view, ← coe_set]

/-- Transport: the support is the specification view's support (`≠ none` is `≠ 0`). -/
theorem toDFinsupp_support [DecidableEq K] [∀ a, DecidableEq (V a)] (m : SparseMap K V) :
    m.toDFinsupp.support = m.support := by
  ext a
  rw [DFinsupp.mem_support_iff, mem_support_iff, toDFinsupp_apply]
  rfl

@[simp] theorem toDFinsupp_zero [DecidableEq K] (a : K) : (0 : SparseMap K V).toDFinsupp a = none :=
  zero_apply a

/-- Transport: the specification view loses nothing. -/
theorem toDFinsupp_injective [DecidableEq K] : Function.Injective (toDFinsupp (K := K) (V := V)) := by
  intro m₁ m₂ h
  refine ext fun a => ?_
  have := DFunLike.congr_fun h a
  simpa only [toDFinsupp_apply] using this

/-! ### Decidable equality -/

instance [∀ a, DecidableEq (V a)] : DecidableEq (SparseMap K V) := fun m₁ m₂ =>
  decidable_of_iff (m₁.tree = m₂.tree) ⟨ext_tree, fun h => h ▸ rfl⟩

end SparseMap

/-! ## Witnesses: kernel evaluation of concrete maps -/

namespace SparseMap.Example

/-- Heterogeneous values over a dependent key: `Nat` keys hold `Nat`, `Bool` keys hold `List Nat`. -/
abbrev Val : (Σ b : Bool, Nat) → Type
  | ⟨false, _⟩ => Nat
  | ⟨true, _⟩ => List Nat

instance valDecEq : (k : Σ b : Bool, Nat) → DecidableEq (Val k)
  | ⟨false, _⟩ => inferInstanceAs (DecidableEq Nat)
  | ⟨true, _⟩ => inferInstanceAs (DecidableEq (List Nat))

abbrev M := SparseMap (Σ b : Bool, Nat) Val

def m₁ : M := ((∅ : M).set ⟨false, 3⟩ (some (7 : Nat))).set ⟨true, 3⟩ (some ([1, 2] : List Nat))
def m₂ : M := ((∅ : M).set ⟨true, 3⟩ (some ([1, 2] : List Nat))).set ⟨false, 3⟩ (some (7 : Nat))

theorem lookup_false : m₁ ⟨false, 3⟩ = some (7 : Nat) := by decide
theorem lookup_true : m₁ ⟨true, 3⟩ = some ([1, 2] : List Nat) := by decide
theorem lookup_absent : m₁ ⟨false, 4⟩ = none := by decide
/-- Equality after differing insertion histories, by kernel evaluation. -/
theorem histories_agree : m₁ = m₂ := by decide
theorem erase_differs : m₁.set ⟨false, 3⟩ none ≠ m₂ := by decide

end SparseMap.Example

#assert_axioms SparseMap.ext
#assert_axioms SparseMap.set_eq
#assert_axioms SparseMap.set_ne
#assert_axioms SparseMap.coe_set
#assert_axioms SparseMap.mem_support_iff
#assert_axioms SparseMap.mem_toList
#assert_axioms SparseMap.filter_apply
#assert_axioms SparseMap.Example.histories_agree

#assert_axioms StoreKey.frame_append_inj
#assert_axioms StoreKey.code_inj
#assert_axioms StoreKey.listCode_injective
#assert_axioms CachedKey.of_value
#assert_axioms CachedKey.eq_of_code_eq
#assert_axioms CachedKey.eq_of
#assert_axioms SparseMap.get?_empty
#assert_axioms SparseMap.emptyc_apply
#assert_axioms SparseMap.coe_apply
#assert_axioms SparseMap.zero_apply
#assert_axioms SparseMap.ext_tree
#assert_axioms SparseMap.ext_iff'
#assert_axioms SparseMap.cmp_of_ne
#assert_axioms SparseMap.set_apply
#assert_axioms SparseMap.set_set
#assert_axioms SparseMap.set_self
#assert_axioms SparseMap.set_comm
#assert_axioms SparseMap.mem_keys
#assert_axioms SparseMap.nodup_keys
#assert_axioms SparseMap.not_mem_support_iff
#assert_axioms SparseMap.toDFinsupp_apply
#assert_axioms SparseMap.toDFinsupp_set
#assert_axioms SparseMap.toDFinsupp_support
#assert_axioms SparseMap.toDFinsupp_zero
#assert_axioms SparseMap.toDFinsupp_injective
#assert_axioms SparseMap.Example.lookup_false
#assert_axioms SparseMap.Example.lookup_true
#assert_axioms SparseMap.Example.lookup_absent
#assert_axioms SparseMap.Example.erase_differs

end Minidregg.Theory
