import Kernel.World
import Compiler.FiniteDependentMapCachedOrdering

/-!
# A World's maps, re-represented without changing a value

`Store.set` is `DFinsupp.update`: the new map's function is `Function.update` of the old one and its support
multiset gains the address. After `n` writes a lookup walks `n` closures and the support carries `n` entries, so a
World folded over a log answers each read in time linear in the log, and the fold is quadratic (a 483-record
Store's open spent 99% of 175 s in `foldRecords`, 86% of it inside `Function.update`). `compactBy` rebuilds the
same map from its support once, as a balanced tree over cached `Nat` keys (`fromEntriesCached`); `compactBy_eq`
says it is the same map, so every statement about the World is untouched.
-/

namespace Minidregg.Compiler.WorldCompact

open Minidregg.Compiler.FiniteDependentMapCachedOrdering
open Minidregg.Compiler.FiniteDependentMapCodec (fromEntries)

section Generic

variable {K : Type} [DecidableEq K] {V : K → Type} [∀ key, Zero (V key)]
  (keyOf : K → Nat) (keyExact : Function.Injective keyOf)

/-- The map read at the keys of `keys`, as a tree. -/
def buildFrom (f : Π₀ key : K, V key) (keys : List K) : Π₀ key : K, V key :=
  fromEntriesCached keyOf keyExact (keys.map fun key => ⟨key, f key⟩)

omit [DecidableEq K] in
theorem fromEntries_map_apply [DecidableEq K] (f : Π₀ key : K, V key) (keys : List K) (key : K) :
    fromEntries (keys.map fun k => (⟨k, f k⟩ : Sigma V)) key = if key ∈ keys then f key else 0 := by
  induction keys with
  | nil => rfl
  | cons head rest ih =>
      by_cases same : key = head
      · subst key
        simp [fromEntries, DFinsupp.update]
      · simp [fromEntries, DFinsupp.update, same, ih]

theorem buildFrom_apply (f : Π₀ key : K, V key) (keys : List K) (key : K) :
    buildFrom keyOf keyExact f keys key = if key ∈ keys then f key else 0 := by
  rw [buildFrom, fromEntriesCached_eq, fromEntries_map_apply]

/-- Rebuild a map from its own support: the same map (`compactBy_eq`), one tree lookup per read. -/
def compactBy (f : Π₀ key : K, V key) : Π₀ key : K, V key :=
  Trunc.lift
    (fun (support : {s : Multiset K // ∀ i, i ∈ s ∨ f i = 0}) =>
      Quot.lift (buildFrom keyOf keyExact f)
        (fun left right (perm : List.Perm left right) => by
          apply DFinsupp.ext
          intro key
          simp only [buildFrom_apply, perm.mem_iff])
        support.1)
    (fun left right => by
      rcases left with ⟨left, leftCovers⟩
      rcases right with ⟨right, rightCovers⟩
      induction left using Quot.induction_on with
      | h leftKeys =>
      induction right using Quot.induction_on with
      | h rightKeys =>
      apply DFinsupp.ext
      intro key
      show buildFrom keyOf keyExact f leftKeys key = buildFrom keyOf keyExact f rightKeys key
      rw [buildFrom_apply, buildFrom_apply]
      rcases leftCovers key with inLeft | zero
      · rcases rightCovers key with inRight | zero
        · simp [show key ∈ leftKeys from inLeft, show key ∈ rightKeys from inRight]
        · split <;> simp [zero]
      · split <;> split <;> simp [zero])
    f.support'

@[simp] theorem compactBy_eq (f : Π₀ key : K, V key) : compactBy keyOf keyExact f = f := by
  apply DFinsupp.ext
  intro key
  unfold compactBy
  rcases f with ⟨toFun, support'⟩
  induction support' using Trunc.induction_on with
  | h support =>
  rcases support with ⟨keys, covers⟩
  induction keys using Quot.induction_on with
  | h keys =>
  show buildFrom keyOf keyExact _ keys key = _
  rw [buildFrom_apply]
  rcases covers key with present | zero
  · simp [show key ∈ keys from present]
  · split <;> simp_all

end Generic

/-! ## The deployed World's two maps -/

open Minidregg.Kernel.World
open Minidregg.Theory.ResourceCost (Lane)

variable {R : Registry}

def laneIndex : Lane → Nat
  | .incidences => 0 | .turnBytes => 1 | .memoryTouches => 2 | .witnessBytes => 3 | .proofWork => 4
  | .storageBytes => 5 | .networkBytes => 6 | .sideEffectCount => 7 | .feeDebit => 8 | .leaseByteBlocks => 9

theorem laneIndex_injective : Function.Injective laneIndex := by
  intro a b; cases a <;> cases b <;> simp [laneIndex]

abbrev Digest := Minidregg.Theory.TypedAuthorization.Digest

def spaceIndex : SysSpace → Nat
  | .journal => 0 | .head => 1 | .retired => 2 | .parent => 3 | .spent => 4 | .allowance => 5

/-- A system address as one `Nat`: six spaces interleaved, each key by its own `Nat`. -/
def sysKey : Minidregg.Theory.Store.Address (sysLayout Digest Digest) → Nat
  | ⟨.journal, (x : Digest)⟩ => 6 * x.value
  | ⟨.head, _⟩ => 1
  | ⟨.retired, (c : CellId)⟩ => 6 * c + 2
  | ⟨.parent, (c : CellId)⟩ => 6 * c + 3
  | ⟨.spent, (d : Digest)⟩ => 6 * d.value + 4
  | ⟨.allowance, (lane : Lane)⟩ => 6 * laneIndex lane + 5

theorem sysKey_injective : Function.Injective sysKey := by
  rintro ⟨s, k⟩ ⟨t, l⟩ equal
  cases s <;> cases t <;> simp only [sysKey] at equal <;> try omega
  case journal.journal | spent.spent =>
    obtain ⟨k⟩ := k; obtain ⟨l⟩ := l
    dsimp only at equal
    have same : k = l := by omega
    subst same; rfl
  case head.head => rfl
  case retired.retired | parent.parent =>
    change Nat at k l
    have same : k = l := by omega
    subst same; rfl
  case allowance.allowance =>
    have same := laneIndex_injective (show laneIndex k = laneIndex l by omega)
    subst same; rfl

/-- The World's cell map and system store rebuilt from their supports: the same World (`compact_eq`). -/
def compact (w : World R Digest Digest) : World R Digest Digest :=
  ⟨compactBy id Function.injective_id w.cells, compactBy sysKey sysKey_injective w.system⟩

@[simp] theorem compact_eq (w : World R Digest Digest) : compact w = w := by
  rcases w with ⟨cells, system⟩
  simp [compact]

/-- Compact every 32nd height: a lookup then walks at most 32 heights' writes before its tree. -/
def compactEvery (height : Nat) (w : World R Digest Digest) : World R Digest Digest :=
  if height % 32 = 0 then compact w else w

@[simp] theorem compactEvery_eq (height : Nat) (w : World R Digest Digest) : compactEvery height w = w := by
  unfold compactEvery; split <;> simp

#assert_axioms compactBy_eq
#assert_axioms compact_eq
#assert_axioms compactEvery_eq

end Minidregg.Compiler.WorldCompact
