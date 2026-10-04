/-
# Kernel.TurnOfIntent -- the turn a deployed intent is: the diff against the held cell

SURPASS §2(b).1, lane T3.  Every Host admission ends in one
`DurableDataIntent.DataIntent`: the 37 `NativeHostReplay.NativeAdmission`
constructors are indexed by it, so one function covers all of them.
`Turn.ofIntent` reads each written cell's canonical post image at its registry
kind and emits the leg as the **difference** against the cell the world holds:

* an absent cell whose post decodes to a cell is a `create` born with the
  post image's ROM part (`romPart`, T3b) plus a leg of allocations of the rest
  from that image;
* a present cell whose post decodes at the same kind is a leg that guards every
  unchanged present address (a read) and modifies every changed one (`write`,
  `allocate`, `free`), in the codec's address order;
* a read guard of the intent is a leg of pure reads over the guarded cell;
* the nullifiers become `spent` keys (`Bridge.key`, injective), the charge is
  the intent's charge with the storage lane replaced by the patch bytes.

The leg is the cut-free normal form of the receiver's local view: it is a fixed
point of G-NORM's `Patch.normalize` (`legPatch_normalize`), so its write
footprint is exactly the addresses that differ (`ofIntent_minimal`, via
`Patch.normalize_writeFootprint_eq_diff`).  A no-op write becomes a read guard.

The derived patch is *stricter* than the durable layer: it is checked against
every namespace's discipline.  `legPatch_valid_iff` says the leg is valid
exactly when **some** guarded patch takes the held store to the post image, so
`Refusal.notAPatch` fires exactly on images no guarded patch reaches -- a
rewrite of an append-only row, or a ROM write into an existing cell.  It never
fires on a birth (`Codec.birthPatch_valid`, `Delta.create_patchOk`): since T3b
a create carries its ROM image, so install's policy-source cell and every
initial-policy birth's are turns.

What `ofIntent` refuses, by name (`Refusal`): an undecodable post image, a kind
change, a removal of a present cell, a post image no guarded patch reaches, a
read guard on an absent cell, and four shape checks the durable preflight
already implies (duplicate write, duplicate leg, no effect, storage above the
charge).

The world-side theorem is `ofIntent_step`: under the world facts the deployed
preflight establishes, `World.step` accepts the derived turn, the post cells
are the decoded post images (`postCell`), and the system cell is the turn's
system patch.  `Kernel.HostRefinesWorld` lifts it to the deployed `Loaded`.
-/
import Kernel.World
import Kernel.DurableDataIntent
import Kernel.DurableReceiver
import Theory.StoreNormalize
import Compiler.StoreCodec
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.Pairing
import Theory.AssertAxioms

namespace Minidregg.Kernel.TurnOfIntent

open Minidregg.Theory.Store
open Minidregg.Kernel.World
open Minidregg.Theory.ResourceCost (Lane Charge)
open Minidregg.Kernel.DurableDataIntent
  (DataIntent DataWrite ReadGuard StableNullifier StableEvent TransactionId DataSnapshot)

set_option autoImplicit false

/-! ## 1. Patches whose operations touch distinct addresses -/

section Distinct

variable {L : Layout.{0, 0, 0}}

/-- An operation's value at its own address depends only on the store there. -/
theorem apply_at_congr {s t : Store L} (op : Op L) (same : s op.address = t op.address) :
    op.apply s op.address = op.apply t op.address := by
  cases op <;> simp_all [Op.apply, Op.address, Store.set_eq]

/-- A patch over distinct addresses is valid when every operation is enabled at
the start store. -/
theorem validFrom_of_distinct : ∀ {s : Store L} {p : Patch L}, (p.map Op.address).Nodup →
    (∀ op ∈ p, op.Enabled s) → Patch.ValidFrom s p
  | _, [], _, _ => trivial
  | s, op :: rest, nd, en => by
      rw [List.map_cons, List.nodup_cons] at nd
      refine ⟨en op (by simp), validFrom_of_distinct nd.2 fun r hr => ?_⟩
      have ne : r.address ≠ op.address := fun e => nd.1 (e ▸ List.mem_map_of_mem hr)
      exact (Op.enabled_congr r (Op.apply_address_ne s op r.address ne).symm).1
        (en r (by simp [hr]))

/-- And conversely: every operation of a valid distinct-address patch is
enabled at the start store. -/
theorem enabled_of_distinct : ∀ {s : Store L} {p : Patch L}, (p.map Op.address).Nodup →
    Patch.ValidFrom s p → ∀ op ∈ p, op.Enabled s
  | _, [], _, _, _, m => by simp at m
  | s, op :: rest, nd, v, r, m => by
      rw [List.map_cons, List.nodup_cons] at nd
      rcases List.mem_cons.mp m with rfl | hr
      · exact v.1
      · have ne : r.address ≠ op.address := fun e => nd.1 (e ▸ List.mem_map_of_mem hr)
        exact (Op.enabled_congr r (Op.apply_address_ne s op r.address ne).symm).2
          (enabled_of_distinct nd.2 v.2 r hr)

/-- The run of a distinct-address patch, pointwise. -/
theorem run_of_distinct : ∀ {s s' : Store L} {p : Patch L}, (p.map Op.address).Nodup →
    (∀ op ∈ p, op.apply s op.address = s' op.address) →
    (∀ b, (∀ op ∈ p, op.address ≠ b) → s b = s' b) → Patch.run s p = s'
  | _, _, [], _, _, miss => DFinsupp.ext fun b => miss b (by simp)
  | s, s', op :: rest, nd, hit, miss => by
      rw [List.map_cons, List.nodup_cons] at nd
      rw [Patch.run_cons]
      apply run_of_distinct nd.2
      · intro r hr
        have ne : r.address ≠ op.address := fun e => nd.1 (e ▸ List.mem_map_of_mem hr)
        rw [apply_at_congr r (Op.apply_address_ne s op r.address ne)]
        exact hit r (by simp [hr])
      · intro b hb
        by_cases e : b = op.address
        · subst e
          exact hit op (by simp)
        · rw [Op.apply_address_ne s op b e]
          refine miss b fun r hr => ?_
          rcases List.mem_cons.mp hr with rfl | hr'
          · exact Ne.symm e
          · exact hb r hr'

/-- `pull` finds nothing to fuse when no later operation shares the address. -/
theorem pull_none_of_distinct (p : Op L) : ∀ (q : Patch L),
    (∀ r ∈ q, r.address ≠ p.address) → Patch.pull p q = none
  | [], _ => rfl
  | r :: rest, h => by
      have ne := h r (by simp)
      have tail := pull_none_of_distinct p rest fun r' hr' => h r' (by simp [hr'])
      simp [Patch.pull, ne, tail]

/-- A distinct-address patch of tidy operations is normal. -/
theorem normal_of_distinct : ∀ {p : Patch L}, (p.map Op.address).Nodup →
    (∀ op ∈ p, op.tidy = op) → Patch.Normal p
  | [], _, _ => trivial
  | op :: rest, nd, td => by
      rw [List.map_cons, List.nodup_cons] at nd
      refine ⟨td op (by simp), pull_none_of_distinct op rest fun r hr e => ?_,
        normal_of_distinct nd.2 fun r hr => td r (by simp [hr])⟩
      exact nd.1 (e ▸ List.mem_map_of_mem hr)

end Distinct

/-! ## 2. The diff of two stores -/

section Diff

variable {L : Layout.{0, 0, 0}}

/-- The guard an address contributes: a read of its unchanged present value. -/
def guardOp (s s' : Store L) (a : Address L) : Option (Op L) :=
  match s a, s' a with
  | some x, some y => if x = y then some (.read a.1 a.2 (some x)) else none
  | _, _ => none

/-- The modification an address contributes: the one operation taking its old
value to its new one, if they differ. -/
def changeOp (s s' : Store L) (a : Address L) : Option (Op L) :=
  match s a, s' a with
  | none, none => none
  | none, some y => some (.allocate a.1 a.2 y)
  | some x, none => some (.free a.1 a.2 x)
  | some x, some y => if x = y then none else some (.write a.1 a.2 x y)

/-- **The diff patch** over an address list: the guards of every unchanged
present address first (so they are the leg's `Leg.guards`), then one
modification per changed address, each group in the list's order. -/
def diff (as : List (Address L)) (s s' : Store L) : Patch L :=
  as.filterMap (guardOp s s') ++ as.filterMap (changeOp s s')

theorem guardOp_spec {s s' : Store L} {a : Address L} {op : Op L}
    (h : guardOp s s' a = some op) :
    ∃ x, s a = some x ∧ s' a = some x ∧ op = .read a.1 a.2 (some x) := by
  unfold guardOp at h
  rcases hs : s a with _ | x <;> rcases hs' : s' a with _ | y <;> simp only [hs, hs'] at h
  · cases h
  · cases h
  · cases h
  · split at h
    · rename_i e
      subst e
      cases h
      exact ⟨x, rfl, rfl, rfl⟩
    · cases h

theorem changeOp_spec {s s' : Store L} {a : Address L} {op : Op L}
    (h : changeOp s s' a = some op) :
    s a ≠ s' a ∧ op.address = a ∧ op.apply s a = s' a ∧ op.tidy = op ∧
      ((s a = none ∧ ∃ y, s' a = some y ∧ op = .allocate a.1 a.2 y) ∨
        (∃ x, s a = some x ∧ s' a = none ∧ op = .free a.1 a.2 x) ∨
        (∃ x y, s a = some x ∧ s' a = some y ∧ x ≠ y ∧ op = .write a.1 a.2 x y)) := by
  unfold changeOp at h
  rcases hs : s a with _ | x <;> rcases hs' : s' a with _ | y <;> simp only [hs, hs'] at h
  · cases h
  · cases h
    refine ⟨by simp, rfl, ?_, rfl, .inl ⟨rfl, y, rfl, rfl⟩⟩
    show (s.set a (some y)) a = some y
    exact Store.set_eq _ _ _
  · cases h
    refine ⟨by simp, rfl, ?_, rfl, .inr (.inl ⟨x, rfl, rfl, rfl⟩)⟩
    show (s.set a none) a = none
    exact Store.set_eq _ _ _
  · split at h
    · cases h
    · rename_i ne
      cases h
      refine ⟨by simp [ne], rfl, ?_, by simp [Op.tidy, ne], .inr (.inr ⟨x, y, rfl, rfl, ne, rfl⟩)⟩
      show (s.set a (some y)) a = some y
      exact Store.set_eq _ _ _

theorem guardOp_address {s s' : Store L} {a : Address L} {op : Op L}
    (h : guardOp s s' a = some op) : op.address = a := by
  obtain ⟨x, -, -, rfl⟩ := guardOp_spec h
  rfl

/-- An address with no modification holds the same value before and after. -/
theorem ops_none {s s' : Store L} {a : Address L}
    (hc : changeOp s s' a = none) : s a = s' a := by
  unfold changeOp at hc
  rcases hs : s a with _ | x <;> rcases hs' : s' a with _ | y <;> simp only [hs, hs'] at hc
  · rfl
  · cases hc
  · cases hc
  · by_cases e : x = y
    · rw [e]
    · simp [e] at hc

theorem guard_change_exclusive {s s' : Store L} {a : Address L} {op op' : Op L}
    (hg : guardOp s s' a = some op) (hc : changeOp s s' a = some op') : False := by
  obtain ⟨x, hs, hs', -⟩ := guardOp_spec hg
  exact (changeOp_spec hc).1 (hs.trans hs'.symm)

theorem map_address_filterMap (f : Address L → Option (Op L))
    (hf : ∀ a op, f a = some op → op.address = a) :
    ∀ as : List (Address L), (as.filterMap f).map Op.address = as.filter fun a => (f a).isSome
  | [] => rfl
  | a :: as => by
      rw [List.filterMap_cons, List.filter_cons]
      cases h : f a with
      | none => simp [map_address_filterMap f hf as]
      | some op => simp [hf a op h, map_address_filterMap f hf as]

theorem mem_diff {as : List (Address L)} {s s' : Store L} {op : Op L} :
    op ∈ diff as s s' ↔ ∃ a ∈ as, guardOp s s' a = some op ∨ changeOp s s' a = some op := by
  unfold diff
  rw [List.mem_append, List.mem_filterMap, List.mem_filterMap]
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
    · exact ⟨a, ha, .inl h⟩
    · exact ⟨a, ha, .inr h⟩
  · rintro ⟨a, ha, h | h⟩
    · exact .inl ⟨a, ha, h⟩
    · exact .inr ⟨a, ha, h⟩

theorem diff_op_address {as : List (Address L)} {s s' : Store L} {op : Op L}
    (m : op ∈ diff as s s') : ∃ a ∈ as, op.address = a ∧
      (guardOp s s' a = some op ∨ changeOp s s' a = some op) := by
  obtain ⟨a, ha, h | h⟩ := mem_diff.mp m
  · exact ⟨a, ha, guardOp_address h, .inl h⟩
  · exact ⟨a, ha, (changeOp_spec h).2.1, .inr h⟩

/-- The diff touches each address at most once. -/
theorem diff_distinct {as : List (Address L)} (nd : as.Nodup) (s s' : Store L) :
    ((diff as s s').map Op.address).Nodup := by
  unfold diff
  rw [List.map_append, map_address_filterMap _ (fun _ _ h => guardOp_address h),
    map_address_filterMap _ (fun _ _ h => (changeOp_spec h).2.1), List.nodup_append]
  refine ⟨nd.filter _, nd.filter _, fun a ha b hb e => ?_⟩
  subst e
  rw [List.mem_filter] at ha hb
  obtain ⟨op, hop⟩ := Option.isSome_iff_exists.mp ha.2
  obtain ⟨op', hop'⟩ := Option.isSome_iff_exists.mp hb.2
  exact guard_change_exclusive hop hop'

/-- **The diff runs to the post store**, whatever the guards say (`run` is
total): every address the list covers ends at its new value. -/
theorem diff_run {as : List (Address L)} (nd : as.Nodup) {s s' : Store L}
    (cover : ∀ a, s a ≠ none ∨ s' a ≠ none → a ∈ as) :
    Patch.run s (diff as s s') = s' := by
  refine run_of_distinct (diff_distinct nd s s') (fun op m => ?_) (fun b hb => ?_)
  · obtain ⟨a, -, ha, h | h⟩ := diff_op_address m
    · obtain ⟨x, hs, hs', rfl⟩ := guardOp_spec h
      exact hs.trans hs'.symm
    · rw [ha]
      exact (changeOp_spec h).2.2.1
  · by_cases hm : b ∈ as
    · apply ops_none
      cases hc : changeOp s s' b with
      | none => rfl
      | some op =>
          exact absurd (changeOp_spec hc).2.1 (hb op (mem_diff.mpr ⟨b, hm, .inr hc⟩))
    · have h1 : s b = none := by
        by_contra h; exact hm (cover b (.inl h))
      have h2 : s' b = none := by
        by_contra h; exact hm (cover b (.inr h))
      rw [h1, h2]

/-- The diff is valid exactly when each modification is enabled at the start
store (the guards always are). -/
theorem diff_validFrom_iff {as : List (Address L)} (nd : as.Nodup) (s s' : Store L) :
    Patch.ValidFrom s (diff as s s') ↔
      ∀ a ∈ as, ∀ op, changeOp s s' a = some op → op.Enabled s := by
  constructor
  · intro v a ha op h
    exact enabled_of_distinct (diff_distinct nd s s') v op (mem_diff.mpr ⟨a, ha, .inr h⟩)
  · intro en
    refine validFrom_of_distinct (diff_distinct nd s s') fun op m => ?_
    obtain ⟨a, ha, h | h⟩ := mem_diff.mp m
    · obtain ⟨x, hs, -, rfl⟩ := guardOp_spec h
      exact hs
    · exact en a ha op h

/-- The diff is in G-NORM's normal form. -/
theorem diff_normal {as : List (Address L)} (nd : as.Nodup) (s s' : Store L) :
    Patch.Normal (diff as s s') := by
  refine normal_of_distinct (diff_distinct nd s s') fun op m => ?_
  obtain ⟨a, -, h | h⟩ := mem_diff.mp m
  · obtain ⟨x, -, -, rfl⟩ := guardOp_spec h
    rfl
  · exact (changeOp_spec h).2.2.2.1

/-- **Expressibility, exactly.**  The diff is valid iff *some* guarded patch
takes `s` to `s'`.  So a diff refused by the discipline is an image no turn's
leg can produce: `rom_preserved` and `appendOnly_present_preserved` are the
only obstructions. -/
theorem diff_valid_iff_executes {as : List (Address L)} (nd : as.Nodup) {s s' : Store L}
    (cover : ∀ a, s a ≠ none ∨ s' a ≠ none → a ∈ as) :
    Patch.ValidFrom s (diff as s s') ↔ ∃ p, Patch.ValidFrom s p ∧ Patch.run s p = s' := by
  constructor
  · intro v
    exact ⟨_, v, diff_run nd cover⟩
  · rintro ⟨p, valid, runs⟩
    rw [diff_validFrom_iff nd]
    intro a _ op h
    obtain ⟨-, -, -, -, hcase⟩ := changeOp_spec h
    rcases hcase with ⟨hs, y, hs', rfl⟩ | ⟨x, hs, hs', rfl⟩ | ⟨x, y, hs, hs', ne, rfl⟩
    · refine ⟨fun hrom => ?_, hs⟩
      have := Patch.rom_preserved s p a valid hrom
      rw [runs, hs, hs'] at this
      cases this
    · refine ⟨?_, hs⟩
      cases hd : L.discipline a.1 with
      | ram => rfl
      | rom =>
          have := Patch.rom_preserved s p a valid hd
          rw [runs, hs, hs'] at this
          cases this
      | appendOnly =>
          have := Patch.appendOnly_present_preserved s p a x valid hd hs
          rw [runs, hs'] at this
          cases this
    · refine ⟨?_, hs⟩
      cases hd : L.discipline a.1 with
      | ram => rfl
      | rom =>
          have := Patch.rom_preserved s p a valid hd
          rw [runs, hs, hs'] at this
          exact absurd (Option.some.inj this).symm ne
      | appendOnly =>
          have := Patch.appendOnly_present_preserved s p a x valid hd hs
          rw [runs, hs'] at this
          exact absurd (Option.some.inj this).symm ne

end Diff

/-! ## 3. Codecs: decoding a cell image at its registry kind -/

/-- What `ofIntent` needs of the deployed cell encoding.  `decode` is
`none` on bytes that do not decode, `some none` on the canonical absent slot,
`some (some cell)` on a cell; `support` enumerates a store's present addresses
in the codec's canonical order (`ofWires` builds it from `StoreCodec.Wire`'s
sorted support). -/
structure Codec (R : Registry) where
  decode : List UInt8 → Option (Option (Cell R))
  support : (k : R.Kind) → Store (R.layout k) → List (Address (R.layout k))
  mem_support : ∀ k s a, a ∈ support k s ↔ s a ≠ none
  support_nodup : ∀ k s, (support k s).Nodup

namespace Codec

variable {R : Registry} (C : Codec R)

/-- The addresses a diff from `s` to `s'` must visit: `s`'s support, then the
addresses only `s'` holds. -/
def cover (k : R.Kind) (s s' : Store (R.layout k)) : List (Address (R.layout k)) :=
  C.support k s ++ (C.support k s').filter fun a => decide (s a = none)

theorem cover_nodup (k : R.Kind) (s s' : Store (R.layout k)) : (C.cover k s s').Nodup := by
  unfold cover
  rw [List.nodup_append]
  refine ⟨C.support_nodup k s, (C.support_nodup k s').filter _, fun a ha b hb e => ?_⟩
  subst e
  rw [List.mem_filter] at hb
  exact (C.mem_support k s a).mp ha (of_decide_eq_true hb.2)

theorem mem_cover {k : R.Kind} {s s' : Store (R.layout k)} (a : Address (R.layout k))
    (h : s a ≠ none ∨ s' a ≠ none) : a ∈ C.cover k s s' := by
  unfold cover
  by_cases hs : s a = none
  · rcases h with h | h
    · exact absurd hs h
    · exact List.mem_append_right _
        (List.mem_filter.mpr ⟨(C.mem_support k s' a).mpr h, decide_eq_true hs⟩)
  · exact List.mem_append_left _ ((C.mem_support k s a).mpr hs)

/-- **The leg patch** taking `s` to `s'` at kind `k`. -/
def legPatch (k : R.Kind) (s s' : Store (R.layout k)) : Patch (R.layout k) :=
  diff (C.cover k s s') s s'

theorem legPatch_run (k : R.Kind) (s s' : Store (R.layout k)) :
    Patch.run s (C.legPatch k s s') = s' :=
  diff_run (C.cover_nodup k s s') fun a h => C.mem_cover a h

/-- The leg patch is a fixed point of G-NORM's normalizer. -/
theorem legPatch_normalize (k : R.Kind) (s s' : Store (R.layout k)) :
    Patch.normalize (C.legPatch k s s') = C.legPatch k s s' :=
  Patch.normalize_of_normal (diff_normal (C.cover_nodup k s s') s s')

theorem legPatch_valid_iff (k : R.Kind) (s s' : Store (R.layout k)) :
    Patch.ValidFrom s (C.legPatch k s s') ↔
      ∃ p, Patch.ValidFrom s p ∧ Patch.run s p = s' :=
  diff_valid_iff_executes (C.cover_nodup k s s') fun a h => C.mem_cover a h

/-- A guard leg (no change) is always valid. -/
theorem legPatch_self_valid (k : R.Kind) (s : Store (R.layout k)) :
    Patch.ValidFrom s (C.legPatch k s s) :=
  (C.legPatch_valid_iff k s s).mpr ⟨[], trivial, rfl⟩

/-- **A birth's leg is always valid (T3b)**: from the born ROM image
`romPart s'`, the leg to `s'` only allocates the non-ROM addresses, each fresh. -/
theorem birthPatch_valid (k : R.Kind) (s' : Store (R.layout k)) :
    Patch.ValidFrom (romPart s') (C.legPatch k (romPart s') s') := by
  unfold legPatch
  rw [diff_validFrom_iff (C.cover_nodup k _ _)]
  intro a _ op h
  obtain ⟨ne, -, -, -, hcase⟩ := changeOp_spec h
  by_cases hrom : (R.layout k).discipline a.1 = .rom
  · exact (ne (by rw [romPart_apply, if_pos hrom])).elim
  · have hnone : romPart s' a = none := by rw [romPart_apply, if_neg hrom]
    rcases hcase with ⟨_, y, _, rfl⟩ | ⟨x, hs, _, _⟩ | ⟨x, y, hs, _, _, _⟩
    · exact ⟨hrom, hnone⟩
    · rw [hnone] at hs; cases hs
    · rw [hnone] at hs; cases hs

/-- A codec from a decoder and one `StoreCodec.Wire` per kind: the support is
the wire's canonical (address-byte) order, so the derived leg's op order is
canonical -- G-NORM's open "op order" gap, closed by the wire. -/
def ofWires (decode : List UInt8 → Option (Option (Cell R)))
    (wire : (k : R.Kind) → Minidregg.Compiler.StoreCodec.Wire (R.layout k)) : Codec R where
  decode := decode
  support k s := Minidregg.Compiler.StoreCodec.sortedSupport (wire k) s
  mem_support k s a := Minidregg.Compiler.StoreCodec.mem_sortedSupport (wire k) s a
  support_nodup k s := by
    rw [Minidregg.Compiler.StoreCodec.sortedSupport_eq]
    exact Finset.sort_nodup _ _

end Codec

/-! ## 4. Nullifier keys -/

/-- An injective code of a byte string. -/
def bytesCode (bytes : List UInt8) : Nat :=
  Encodable.encode (bytes.map UInt8.toNat)

theorem bytesCode_injective : Function.Injective bytesCode := by
  intro a b h
  have e : a.map UInt8.toNat = b.map UInt8.toNat := Encodable.encode_injective h
  exact (List.map_injective_iff.mpr fun x y hxy => UInt8.toNat_inj.mp hxy) e

/-- **An injective nullifier code**: every field of the stable nullifier,
including its canonical bytes, by `Nat.pair`.  No hash, so no collision
premise: `spent` keyed by it is the deployed consumed set exactly. -/
def nullifierCode (n : StableNullifier) : Nat :=
  Nat.pair n.codecVersion
    (Nat.pair n.domain.value (Nat.pair n.nullifierId.value (bytesCode n.canonicalBytes)))

theorem nullifierCode_injective : Function.Injective nullifierCode := by
  rintro ⟨v, ⟨d⟩, ⟨i⟩, b⟩ ⟨v', ⟨d'⟩, ⟨i'⟩, b'⟩ h
  simp only [nullifierCode, Nat.pair_eq_pair] at h
  obtain ⟨rfl, rfl, rfl, hb⟩ := h
  rw [bytesCode_injective hb]

/-- The bridge between the deployed objects and the model: the cell codec and
an injective nullifier key. -/
structure Bridge (R : Registry) (D : Type) where
  codec : Codec R
  key : StableNullifier → D
  key_injective : Function.Injective key

/-- The deployed digest key: `⟨nullifierCode n⟩`. -/
def digestKey (n : StableNullifier) : Theory.TypedAuthorization.Digest := ⟨nullifierCode n⟩

theorem digestKey_injective : Function.Injective digestKey := by
  intro a b h
  exact nullifierCode_injective (Theory.TypedAuthorization.Digest.mk.inj h)

/-! ## 5. The derived turn -/

section Derive

variable {R : Registry} {D : Type} [DecidableEq D]
variable {rootBytes : List UInt8 → Theory.TypedAuthorization.Digest}

/-- The turn type the deployed intents land in. -/
abbrev DTurn (R : Registry) (D : Type) := Turn R TransactionId StableEvent D

/-- What one written cell is, read against the cell the world holds. -/
inductive Delta (R : Registry)
  | absent
  | create (k : R.Kind) (post : Store (R.layout k))
  | change (k : R.Kind) (pre post : Store (R.layout k))

/-- Why an admitted intent has no turn. -/
inductive Refusal
  /-- A written post image does not decode at any registry kind. -/
  | undecodable (cell : CellId)
  /-- A written post image decodes at a different kind than the held cell. -/
  | kindChanged (cell : CellId)
  /-- A written post image is the absent slot over a present cell. -/
  | removed (cell : CellId)
  /-- No guarded patch takes the held store to the post image
  (`Codec.legPatch_valid_iff`): an append-only row rewritten, a RAM-only op in
  an append-only namespace, a ROM address written or born. -/
  | notAPatch (cell : CellId)
  /-- A read guard names an absent cell: a leg cannot pin absence. -/
  | guardOnAbsent (cell : CellId)
  | duplicateWrite
  | duplicateLeg
  | noEffect
  | storageAboveCharge
  deriving DecidableEq, Repr

/-- The refusal an `Except` carries, if any. -/
def refusalOf {α : Type} : Except Refusal α → Option Refusal
  | .error r => some r
  | .ok _ => none

/-- Read one write against the held cells. -/
def deltaOf (C : Codec R) (cells : CellId → Option (Cell R)) (w : DataWrite) :
    Except Refusal (Delta R) :=
  match C.decode w.canonicalPostBytes with
  | none => .error (.undecodable w.cellId.value)
  | some post =>
      match cells w.cellId.value, post with
      | none, none => .ok .absent
      | none, some p => .ok (.create p.kind p.store)
      | some _, none => .error (.removed w.cellId.value)
      | some pre, some p =>
          match p.storeAt pre.kind with
          | none => .error (.kindChanged w.cellId.value)
          | some s' => .ok (.change pre.kind pre.store s')

/-- Whether a delta's leg patch is valid from its pre store (a birth's is the
born ROM image). -/
def Delta.patchOk (C : Codec R) : Delta R → Bool
  | .absent => true
  | .create k s' => decide (Patch.ValidFrom (romPart s') (C.legPatch k (romPart s') s'))
  | .change k s s' => decide (Patch.ValidFrom s (C.legPatch k s s'))

/-- The create a delta contributes: the cell born with the post image's ROM
part (T3b). -/
def Delta.create? (c : CellId) : Delta R → Option (CellId × Cell R × Option CellId)
  | .create k s' => some (c, ⟨k, romPart s'⟩, none)
  | _ => none

/-- The leg a delta contributes. -/
def Delta.leg? (C : Codec R) (c : CellId) : Delta R → Option (Leg R)
  | .absent => none
  | .create k s' => some ⟨c, k, C.legPatch k (romPart s') s'⟩
  | .change k s s' => some ⟨c, k, C.legPatch k s s'⟩

/-- A birth is never `notAPatch` (T3b). -/
theorem Delta.create_patchOk (C : Codec R) (k : R.Kind) (s' : Store (R.layout k)) :
    (Delta.create k s').patchOk C = true :=
  decide_eq_true (C.birthPatch_valid k s')

/-- The first refusal one write carries, if any. -/
def writeRefusal (C : Codec R) (cells : CellId → Option (Cell R)) (w : DataWrite) :
    Option Refusal :=
  match deltaOf C cells w with
  | .error e => some e
  | .ok δ => if δ.patchOk C then none else some (.notAPatch w.cellId.value)

/-- The written cells with their deltas. -/
def deltas (C : Codec R) (cells : CellId → Option (Cell R)) (ws : List DataWrite) :
    List (CellId × Delta R) :=
  ws.filterMap fun w =>
    match deltaOf C cells w with
    | .ok δ => some (w.cellId.value, δ)
    | .error _ => none

/-- The written cell ids. -/
def writeIds (ws : List DataWrite) : List CellId := ws.map fun w => w.cellId.value

/-- The guarded cells, each once, never a written one. -/
def guardIds (ws : List DataWrite) (gs : List ReadGuard) : List CellId :=
  (gs.map fun g => g.cellId.value).eraseDups.filter fun c => c ∉ writeIds ws

/-- The guard leg of a held cell: a read of every present address. -/
def guardLeg (C : Codec R) (cells : CellId → Option (Cell R)) (c : CellId) : Option (Leg R) :=
  (cells c).map fun cell => ⟨c, cell.kind, C.legPatch cell.kind cell.store cell.store⟩

/-- The storage bytes of creates and legs: the legs' bytes plus the born
images' (`World.patchBytes`). -/
def storageOf (H : History R TransactionId StableEvent D)
    (creates : List (CellId × Cell R × Option CellId)) (legs : List (Leg R)) : Nat :=
  (legs.map H.legBytes).sum + (creates.map fun c => H.imageBytes c.2.1).sum

/-- The turn's charge: the intent's, with the storage lane the patch bytes. -/
def chargeOf (H : History R TransactionId StableEvent D)
    (creates : List (CellId × Cell R × Option CellId)) (legs : List (Leg R)) (exact : Charge) :
    Charge :=
  fun l => if l = .storageBytes then storageOf H creates legs else exact l

/-- The creates of an intent. -/
def createsOf (C : Codec R) (cells : CellId → Option (Cell R)) (intent : DataIntent rootBytes) :
    List (CellId × Cell R × Option CellId) :=
  (deltas C cells intent.writes).filterMap fun d => d.2.create? d.1

/-- The legs of an intent: guard legs, then write legs. -/
def legsOf (C : Codec R) (cells : CellId → Option (Cell R)) (intent : DataIntent rootBytes) :
    List (Leg R) :=
  (guardIds intent.writes intent.readGuards).filterMap (guardLeg C cells) ++
    (deltas C cells intent.writes).filterMap fun d => d.2.leg? C d.1

/-- The turn record of an intent (no checks). -/
def turnOf (B : Bridge R D) (H : History R TransactionId StableEvent D)
    (cells : CellId → Option (Cell R)) (intent : DataIntent rootBytes) : DTurn R D :=
  { txId := intent.transactionId
    creates := createsOf B.codec cells intent
    legs := legsOf B.codec cells intent
    retires := []
    event := intent.event
    nullifiers := intent.nullifiers.map B.key
    charge := chargeOf H (createsOf B.codec cells intent) (legsOf B.codec cells intent)
      intent.exactCharge
    subject := intent.subject }

/-- **The derived turn** against held cells.  Every check is named; the first
two groups are the expressibility refusals, the last four are shape checks the
deployed preflight already implies. -/
def ofCells (B : Bridge R D) (H : History R TransactionId StableEvent D)
    (cells : CellId → Option (Cell R)) (intent : DataIntent rootBytes) :
    Except Refusal (DTurn R D) :=
  match intent.writes.findSome? (writeRefusal B.codec cells) with
  | some e => .error e
  | none =>
      match (guardIds intent.writes intent.readGuards).find? (fun c => (cells c).isNone) with
      | some c => .error (.guardOnAbsent c)
      | none =>
          let t := turnOf B H cells intent
          if ¬ (writeIds intent.writes).Nodup then .error .duplicateWrite
          else if ¬ (t.creates.map Prod.fst).Nodup then .error .duplicateWrite
          else if ¬ (t.legs.map Leg.cell).Nodup then .error .duplicateLeg
          else if t.legs.isEmpty ∧ t.creates.isEmpty then .error .noEffect
          else if storageOf H t.creates t.legs > intent.exactCharge .storageBytes then
            .error .storageAboveCharge
          else .ok t

/-- **`Turn.ofIntent`**: the turn an admitted intent is, against the cells the
world holds. -/
def Turn.ofIntent (B : Bridge R D) (H : History R TransactionId StableEvent D)
    (w : World R TransactionId D) (intent : DataIntent rootBytes) : Except Refusal (DTurn R D) :=
  ofCells B H (fun c => w.cells c) intent

/-- What an accepted derivation establishes. -/
structure Derived (B : Bridge R D) (H : History R TransactionId StableEvent D)
    (cells : CellId → Option (Cell R)) (intent : DataIntent rootBytes) (t : DTurn R D) : Prop where
  eq : t = turnOf B H cells intent
  writes_ok : ∀ w ∈ intent.writes, writeRefusal B.codec cells w = none
  guards_present : ∀ c ∈ guardIds intent.writes intent.readGuards, (cells c).isSome = true
  writes_nodup : (writeIds intent.writes).Nodup
  creates_nodup : (t.creates.map Prod.fst).Nodup
  legs_nodup : (t.legs.map Leg.cell).Nodup
  nonempty : ¬ (t.legs.isEmpty = true ∧ t.creates.isEmpty = true)
  storage : storageOf H t.creates t.legs ≤ intent.exactCharge .storageBytes

omit [DecidableEq D] in
theorem ofCells_ok {B : Bridge R D} {H : History R TransactionId StableEvent D}
    {cells : CellId → Option (Cell R)} {intent : DataIntent rootBytes} {t : DTurn R D}
    (h : ofCells B H cells intent = .ok t) : Derived B H cells intent t := by
  unfold ofCells at h
  split at h
  · cases h
  rename_i hw
  split at h
  · cases h
  rename_i hg
  simp only at h
  split_ifs at h with h1 h2 h3 h4 h5
  cases h
  refine ⟨rfl, fun w m => List.findSome?_eq_none_iff.mp hw w m, fun c m => ?_,
    h1, h2, h3, h4, Nat.le_of_not_gt h5⟩
  have := List.find?_eq_none.mp hg c m
  exact Option.isSome_iff_ne_none.mpr (by simpa using this)

/-! ### Reading a derived turn -/

theorem deltaOf_spec {C : Codec R} {cells : CellId → Option (Cell R)} {w : DataWrite}
    {δ : Delta R} (h : deltaOf C cells w = .ok δ) :
    match δ with
    | .absent => cells w.cellId.value = none ∧ C.decode w.canonicalPostBytes = some none
    | .create k s' => cells w.cellId.value = none ∧
        C.decode w.canonicalPostBytes = some (some ⟨k, s'⟩)
    | .change k s s' => cells w.cellId.value = some ⟨k, s⟩ ∧
        C.decode w.canonicalPostBytes = some (some ⟨k, s'⟩) := by
  unfold deltaOf at h
  rcases hd : C.decode w.canonicalPostBytes with _ | post
  · simp only [hd] at h; cases h
  simp only [hd] at h
  rcases hc : cells w.cellId.value with _ | pre <;> rcases post with _ | p <;>
    simp only [hc] at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h; exact ⟨rfl, rfl⟩
  · cases h
  · rcases hs : p.storeAt pre.kind with _ | s' <;> simp only [hs] at h
    · cases h
    · cases h
      exact ⟨rfl, by rw [Cell.eq_of_storeAt hs]⟩

theorem mem_deltas {C : Codec R} {cells : CellId → Option (Cell R)} {ws : List DataWrite}
    {c : CellId} {δ : Delta R} :
    (c, δ) ∈ deltas C cells ws ↔ ∃ w ∈ ws, w.cellId.value = c ∧ deltaOf C cells w = .ok δ := by
  unfold deltas
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨w, hw, h⟩
    split at h
    · rename_i δ' hδ
      cases h
      exact ⟨w, hw, rfl, hδ⟩
    · cases h
  · rintro ⟨w, hw, rfl, hδ⟩
    exact ⟨w, hw, by rw [hδ]⟩

omit [DecidableEq D] in
/-- Each write has its delta in the list. -/
theorem delta_of_write {B : Bridge R D} {H : History R TransactionId StableEvent D}
    {cells : CellId → Option (Cell R)} {intent : DataIntent rootBytes} {t : DTurn R D}
    (d : Derived B H cells intent t) {w : DataWrite} (hw : w ∈ intent.writes) :
    ∃ δ, deltaOf B.codec cells w = .ok δ ∧ δ.patchOk B.codec = true ∧
      (w.cellId.value, δ) ∈ deltas B.codec cells intent.writes := by
  have h := d.writes_ok w hw
  unfold writeRefusal at h
  split at h
  · cases h
  · rename_i δ hδ
    split at h
    · rename_i ok
      exact ⟨δ, hδ, ok, mem_deltas.mpr ⟨w, hw, rfl, hδ⟩⟩
    · cases h

omit [DecidableEq D] in
/-- One delta per written cell. -/
theorem deltas_unique {B : Bridge R D} {H : History R TransactionId StableEvent D}
    {cells : CellId → Option (Cell R)} {intent : DataIntent rootBytes} {t : DTurn R D}
    (d : Derived B H cells intent t) {c : CellId} {δ δ' : Delta R}
    (m : (c, δ) ∈ deltas B.codec cells intent.writes)
    (m' : (c, δ') ∈ deltas B.codec cells intent.writes) : δ = δ' := by
  obtain ⟨w, hw, rfl, hδ⟩ := mem_deltas.mp m
  obtain ⟨w', hw', e, hδ'⟩ := mem_deltas.mp m'
  have := List.inj_on_of_nodup_map d.writes_nodup hw' hw e
  subst this
  rw [hδ] at hδ'
  exact Except.ok.inj hδ'

theorem mem_createsOf {C : Codec R} {cells : CellId → Option (Cell R)}
    {intent : DataIntent rootBytes} {x : CellId × Cell R × Option CellId} :
    x ∈ createsOf C cells intent ↔
      ∃ c k s', (c, Delta.create k s') ∈ deltas C cells intent.writes ∧
        x = (c, ⟨k, romPart s'⟩, none) := by
  unfold createsOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨c, δ⟩, m, h⟩
    cases δ with
    | create k s' => cases h; exact ⟨c, k, s', m, rfl⟩
    | absent => cases h
    | change => cases h
  · rintro ⟨c, k, s', m, rfl⟩
    exact ⟨_, m, rfl⟩

theorem mem_legsOf {C : Codec R} {cells : CellId → Option (Cell R)}
    {intent : DataIntent rootBytes} {leg : Leg R} :
    leg ∈ legsOf C cells intent ↔
      (∃ c ∈ guardIds intent.writes intent.readGuards, ∃ cell, cells c = some cell ∧
          leg = ⟨c, cell.kind, C.legPatch cell.kind cell.store cell.store⟩) ∨
      (∃ c δ, (c, δ) ∈ deltas C cells intent.writes ∧ δ.leg? C c = some leg) := by
  unfold legsOf
  rw [List.mem_append, List.mem_filterMap, List.mem_filterMap]
  constructor
  · rintro (⟨c, m, h⟩ | ⟨⟨c, δ⟩, m, h⟩)
    · unfold guardLeg at h
      rcases hc : cells c with _ | cell
      · rw [hc] at h; cases h
      · rw [hc] at h
        cases h
        exact .inl ⟨c, m, cell, hc, rfl⟩
    · exact .inr ⟨c, δ, m, h⟩
  · rintro (⟨c, m, cell, hc, rfl⟩ | ⟨c, δ, m, h⟩)
    · exact .inl ⟨c, m, by simp [guardLeg, hc]⟩
    · exact .inr ⟨(c, δ), m, h⟩

theorem leg?_cell {C : Codec R} {c : CellId} {δ : Delta R} {leg : Leg R}
    (h : δ.leg? C c = some leg) : leg.cell = c := by
  cases δ <;> simp [Delta.leg?] at h <;> rw [← h]

theorem guardIds_not_written {ws : List DataWrite} {gs : List ReadGuard} {c : CellId}
    (m : c ∈ guardIds ws gs) : c ∉ writeIds ws := by
  unfold guardIds at m
  rw [List.mem_filter] at m
  simpa using m.2

theorem deltas_written {C : Codec R} {cells : CellId → Option (Cell R)} {ws : List DataWrite}
    {c : CellId} {δ : Delta R} (m : (c, δ) ∈ deltas C cells ws) : c ∈ writeIds ws := by
  obtain ⟨w, hw, rfl, -⟩ := mem_deltas.mp m
  exact List.mem_map_of_mem hw

/-! ## 6. `ofIntent_minimal`: the leg is the normal form, its footprint the diff -/

/-- **`ofIntent_minimal`.**  Every leg of a derived turn is a fixed point of
G-NORM's `Patch.normalize`, so from any store it is valid at, its write
footprint is exactly the addresses whose value it changes
(`Patch.normalize_writeFootprint_eq_diff`): a no-op write is a read guard, and
nothing else is written. -/
theorem ofIntent_minimal {B : Bridge R D} {H : History R TransactionId StableEvent D}
    {w : World R TransactionId D} {intent : DataIntent rootBytes} {t : DTurn R D}
    (h : Turn.ofIntent B H w intent = .ok t) {leg : Leg R} (m : leg ∈ t.legs) :
    Patch.normalize leg.patch = leg.patch ∧
      ∀ pre, Patch.ValidFrom pre leg.patch →
        (↑(Patch.writeFootprint leg.patch) : Set (Address (R.layout leg.kind))) =
          {a | Patch.run pre leg.patch a ≠ pre a} := by
  have d := ofCells_ok h
  have fixed : Patch.normalize leg.patch = leg.patch := by
    rw [d.eq] at m
    rcases mem_legsOf.mp m with ⟨c, -, cell, -, rfl⟩ | ⟨c, δ, -, hl⟩
    · exact B.codec.legPatch_normalize _ _ _
    · cases δ <;> simp [Delta.leg?] at hl <;> rw [← hl] <;>
        exact B.codec.legPatch_normalize _ _ _
  refine ⟨fixed, fun pre valid => ?_⟩
  have := Patch.normalize_writeFootprint_eq_diff valid
  rwa [fixed] at this

/-! ## 7. `ofIntent_step`: the world accepts the derived turn -/

/-- The post cell an intent leaves at `c`: its decoded post image when it writes
`c`, else the held cell. -/
def postCell (C : Codec R) (cells : CellId → Option (Cell R)) (intent : DataIntent rootBytes)
    (c : CellId) : Option (Cell R) :=
  match DataSnapshot.lookupPostBytes ⟨c⟩ intent.writes with
  | some bytes => (C.decode bytes).getD (cells c)
  | none => cells c

theorem applyCreates_exists : ∀ (cells : Cells R) (cs : List (CellId × Cell R × Option CellId)),
    (cs.map Prod.fst).Nodup →
    (∀ x ∈ cs, x.2.2 = none ∧ cells x.1 = none ∧ RomOnly x.2.1.store) →
    ∃ cells', applyCreates cells cs = .ok cells'
  | cells, [], _, _ => ⟨cells, rfl⟩
  | cells, (c, k, p) :: rest, nd, h => by
      rw [List.map_cons, List.nodup_cons] at nd
      obtain ⟨hp, hc, hrom⟩ := h (c, k, p) (by simp)
      simp only at hp hc hrom
      subst hp
      obtain ⟨cells', h'⟩ := applyCreates_exists (cells.update c (some k)) rest nd.2
        fun x hx => ⟨(h x (by simp [hx])).1, by
          rw [cells_update_ne _ _ (fun e => nd.1 (by
            simpa [← e] using List.mem_map_of_mem (f := Prod.fst) hx))]
          exact (h x (by simp [hx])).2.1, (h x (by simp [hx])).2.2⟩
      exact ⟨cells', by simp only [applyCreates, hc, roomPresent, if_pos hrom]; exact h'⟩

theorem applyLegs_exists : ∀ (cells : Cells R) (legs : List (Leg R)), (legs.map Leg.cell).Nodup →
    (∀ leg ∈ legs, ∃ pre, cells leg.cell = some ⟨leg.kind, pre⟩ ∧ Patch.ValidFrom pre leg.patch) →
    ∃ cells', applyLegs cells legs = .ok cells'
  | cells, [], _, _ => ⟨cells, rfl⟩
  | cells, leg :: rest, nd, h => by
      rw [List.map_cons, List.nodup_cons] at nd
      obtain ⟨pre, hc, hv⟩ := h leg (by simp)
      have hfd : Patch.firstDisabled? pre leg.patch = none :=
        (Patch.firstDisabled?_eq_none_iff _ _).2 hv
      have ha : applyLeg cells leg =
          .ok (cells.update leg.cell (some ⟨leg.kind, Patch.run pre leg.patch⟩)) := by
        unfold applyLeg
        simp only [hc, Cell.storeAt_self, hfd]
      obtain ⟨cells', h'⟩ := applyLegs_exists
        (cells.update leg.cell (some ⟨leg.kind, Patch.run pre leg.patch⟩)) rest nd.2 fun l hl => by
        obtain ⟨p, hp, hv'⟩ := h l (by simp [hl])
        refine ⟨p, ?_, hv'⟩
        rw [cells_update_ne (c := leg.cell) (x := l.cell) _ _
          (fun e => nd.1 (by rw [← e]; exact List.mem_map_of_mem hl))]
        exact hp
      exact ⟨cells', by simp only [applyLegs, ha]; exact h'⟩

/-- The system core of a turn whose creates name no room and which retires
nothing: the retired guards, the journal row, the head. -/
theorem sysCore_unroomed (H : History R TransactionId StableEvent D) {t : DTurn R D}
    {height : Nat} {logRoot : D} (hrows : t.parentRows = []) (hr : t.retires = []) :
    sysCore H t height logRoot =
      t.creates.map (fun c => Op.read (L := sysLayout TransactionId D) SysSpace.retired c.1 none) ++
        [Op.allocate (L := sysLayout TransactionId D) SysSpace.journal t.txId (height, H.turnDigest t),
          Op.write (L := sysLayout TransactionId D) SysSpace.head () (height, logRoot)
            (height + 1, H.chain logRoot (H.turnDigest t))] := by
  unfold sysCore
  rw [hrows, hr]
  simp only [List.map_nil, List.append_nil, List.append_assoc, List.singleton_append]
  rfl

/-- The system patch of a turn whose creates name no room and which retires
nothing is valid when the journal id is fresh, the head is where the patch
quotes it, the created ids are unretired, the nullifiers are fresh and
distinct, and every charged lane holds the meter value. -/
theorem sysPatch_valid_unroomed (H : History R TransactionId StableEvent D)
    {s : Store (sysLayout TransactionId D)} {t : DTurn R D}
    {height : Nat} {logRoot : D} {avail : Charge}
    (hrooms : ∀ c ∈ t.creates, c.2.2 = none) (hr : t.retires = [])
    (hret : ∀ c ∈ t.creates, s ⟨SysSpace.retired, c.1⟩ = none)
    (hj : s ⟨SysSpace.journal, t.txId⟩ = none)
    (hh : s ⟨SysSpace.head, ()⟩ = some (height, logRoot))
    (hn : t.nullifiers.Nodup ∧ ∀ n ∈ t.nullifiers, s ⟨SysSpace.spent, n⟩ = none)
    (hm : ∀ l, t.charge l ≠ 0 → s ⟨SysSpace.allowance, l⟩ = some (avail l)) :
    Patch.ValidFrom s (sysPatch H t height logRoot avail) := by
  have hrows : t.parentRows = [] := by
    unfold Turn.parentRows
    rw [List.filterMap_eq_nil_iff]
    intro c m
    rw [hrooms c m]
    rfl
  rw [validFrom_sysPatch]
  refine ⟨?_, ?_, ?_⟩
  · rw [sysCore_unroomed H hrows hr, Patch.validFrom_append, run_createReads]
    refine ⟨(validFrom_createReads s t.creates).2 hret, ⟨fun e => Discipline.noConfusion e, hj⟩,
      ⟨rfl, ?_⟩, trivial⟩
    show (s.set ⟨SysSpace.journal, t.txId⟩ (some (height, H.turnDigest t))) ⟨SysSpace.head, ()⟩ = _
    rw [Store.set_ne _ _ _ _ (sys_space_ne (fun e => SysSpace.noConfusion e)), hh]
    rfl
  · rw [validFrom_spentAllocs]
    exact ⟨hn.1, fun n m => (run_sysCore_spent H s t height logRoot n).trans (hn.2 n m)⟩
  · rw [validFrom_debits _ _ _ _ (chargedLanes_nodup _)]
    intro l m
    rw [run_spentAllocs_ne _ _ _ (fun e => SysSpace.noConfusion e), run_sysCore_allowance]
    exact hm l (mem_chargedLanes.mp m)

omit [DecidableEq D] in
theorem patchOk_of_mem {B : Bridge R D} {H : History R TransactionId StableEvent D}
    {cells : CellId → Option (Cell R)} {intent : DataIntent rootBytes} {t : DTurn R D}
    (d : Derived B H cells intent t) {c : CellId} {δ : Delta R}
    (m : (c, δ) ∈ deltas B.codec cells intent.writes) : δ.patchOk B.codec = true := by
  obtain ⟨w0, hw, rfl, hδ⟩ := mem_deltas.mp m
  obtain ⟨δ', hδ', ok, -⟩ := delta_of_write d hw
  rw [hδ] at hδ'
  cases Except.ok.inj hδ'
  exact ok

theorem postCell_written {C : Codec R} {cells : CellId → Option (Cell R)}
    {intent : DataIntent rootBytes} (nd : (writeIds intent.writes).Nodup)
    {w0 : DataWrite} (hw : w0 ∈ intent.writes) {v : Option (Cell R)}
    (hv : C.decode w0.canonicalPostBytes = some v) :
    postCell C cells intent w0.cellId.value = v := by
  have nd' : (intent.writes.map DataWrite.cellId).Nodup :=
    List.Nodup.of_map Theory.TypedAuthorization.Digest.value (by simpa [writeIds, List.map_map] using nd)
  have look := DataSnapshot.lookupPostBytes_of_member intent.writes nd' w0 hw
  unfold postCell
  rw [show (⟨w0.cellId.value⟩ : Theory.TypedAuthorization.Digest) = w0.cellId from rfl, look]
  show (C.decode w0.canonicalPostBytes).getD _ = v
  rw [hv]
  rfl

theorem postCell_unwritten {C : Codec R} {cells : CellId → Option (Cell R)}
    {intent : DataIntent rootBytes} {c : CellId} (hc : c ∉ writeIds intent.writes) :
    postCell C cells intent c = cells c := by
  have miss : (⟨c⟩ : Theory.TypedAuthorization.Digest) ∉ intent.writes.map DataWrite.cellId := by
    intro m
    obtain ⟨w0, hw, e⟩ := List.mem_map.mp m
    exact hc (List.mem_map.mpr ⟨w0, hw, by rw [e]⟩)
  unfold postCell
  rw [DurableReceiver.lookupPostBytes_missing intent.writes _ miss]

/-- **`ofCells_step`**: `ofIntent_step` against any held-cell function that
agrees with the world. -/
theorem ofCells_step (B : Bridge R D) (H : History R TransactionId StableEvent D)
    {w : World R TransactionId D} {cells : CellId → Option (Cell R)}
    (hcells : ∀ c, w.cells c = cells c)
    {intent : DataIntent rootBytes} {t : DTurn R D}
    (derived : ofCells B H cells intent = .ok t)
    {height : Nat} {logRoot : D} (hh : w.head = some (height, logRoot))
    (fresh : w.journal intent.transactionId = none)
    (nodup : intent.nullifiers.Nodup)
    (unspent : ∀ n ∈ intent.nullifiers, w.spent (B.key n) = none)
    (funded : ∀ l, l ≠ .storageBytes → intent.exactCharge l ≤ w.meter l)
    (fundedStorage : intent.exactCharge .storageBytes ≤ w.meter .storageBytes)
    (unretired : ∀ c, w.retired c = none) :
    ∃ w', World.step H w t = some w' ∧
      (∀ c, w'.cells c = postCell B.codec cells intent c) ∧
      w'.system = Patch.run w.system (sysPatch H t height logRoot w.meter) := by
  have d := ofCells_ok derived
  have teq := d.eq
  have hcreates : t.creates = createsOf B.codec cells intent := by rw [teq]; rfl
  have hlegs : t.legs = legsOf B.codec cells intent := by rw [teq]; rfl
  have hretires : t.retires = [] := by rw [teq]; rfl
  have htx : t.txId = intent.transactionId := by rw [teq]; rfl
  have hnull : t.nullifiers = intent.nullifiers.map B.key := by rw [teq]; rfl
  have hcharge : t.charge = chargeOf H t.creates t.legs intent.exactCharge := by
    rw [teq]; rfl
  have hnb : t.notBefore = 0 := by rw [teq]; rfl
  have hvu : t.validUntil = none := by rw [teq]; rfl
  -- creates
  have creates_spec : ∀ x ∈ t.creates, x.2.2 = none ∧ w.cells x.1 = none ∧
      RomOnly x.2.1.store := by
    intro x m
    rw [hcreates] at m
    obtain ⟨c, k, s', m', rfl⟩ := mem_createsOf.mp m
    obtain ⟨w0, -, rfl, hδ⟩ := mem_deltas.mp m'
    exact ⟨rfl, (hcells _).trans (deltaOf_spec hδ).1, romPart_romOnly s'⟩
  have created_iff : ∀ c, c ∈ t.creates.map Prod.fst ↔
      ∃ k s', (c, Delta.create k s') ∈ deltas B.codec cells intent.writes := by
    intro c
    constructor
    · intro m
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp m
      rw [hcreates] at hx
      obtain ⟨c', k, s', m', rfl⟩ := mem_createsOf.mp hx
      exact ⟨k, s', m'⟩
    · rintro ⟨k, s', m⟩
      exact List.mem_map.mpr ⟨(c, ⟨k, romPart s'⟩, none), by
        rw [hcreates]; exact mem_createsOf.mpr ⟨c, k, s', m, rfl⟩, rfl⟩
  have created_written : ∀ c, c ∈ t.creates.map Prod.fst → c ∈ writeIds intent.writes := by
    intro c m
    obtain ⟨k, s', m'⟩ := (created_iff c).mp m
    exact deltas_written m'
  obtain ⟨c1, h1⟩ := applyCreates_exists w.cells t.creates d.creates_nodup
    fun x m => creates_spec x m
  have c1_created : ∀ c k s', (c, Delta.create k s') ∈ deltas B.codec cells intent.writes →
      c1 c = some ⟨k, romPart s'⟩ := by
    intro c k s' m
    have mc : (c, (⟨k, romPart s'⟩ : Cell R), none) ∈ t.creates := by
      rw [hcreates]; exact mem_createsOf.mpr ⟨c, k, s', m, rfl⟩
    exact (applyCreates_mem h1 d.creates_nodup c _ none mc).2
  have c1_frame : ∀ c, c ∉ t.creates.map Prod.fst → c1 c = w.cells c :=
    fun c hc => applyCreates_frame h1 c hc
  -- each leg's pre store in `c1`
  have legs_pre : ∀ leg ∈ t.legs, ∃ pre, c1 leg.cell = some ⟨leg.kind, pre⟩ ∧
      Patch.ValidFrom pre leg.patch := by
    intro leg m
    rw [hlegs] at m
    rcases mem_legsOf.mp m with ⟨c, mg, cell, hc, rfl⟩ | ⟨c, δ, md, hl⟩
    · refine ⟨cell.store, ?_, B.codec.legPatch_self_valid _ _⟩
      have nc : c ∉ t.creates.map Prod.fst := fun m' =>
        guardIds_not_written mg (created_written c m')
      rw [c1_frame c nc, hcells, hc]
    · have ok := patchOk_of_mem d md
      obtain ⟨w0, -, rfl, hδ⟩ := mem_deltas.mp md
      have spec := deltaOf_spec hδ
      cases δ with
      | absent => cases hl
      | create k s' =>
          simp only [Delta.leg?, Option.some.injEq] at hl
          subst hl
          exact ⟨romPart s', c1_created _ k s' md, of_decide_eq_true ok⟩
      | change k s s' =>
          simp only [Delta.leg?, Option.some.injEq] at hl
          subst hl
          refine ⟨s, ?_, of_decide_eq_true ok⟩
          have nc : w0.cellId.value ∉ t.creates.map Prod.fst := by
            intro m'
            obtain ⟨k', s'', m''⟩ := (created_iff _).mp m'
            cases deltas_unique d md m''
          rw [c1_frame _ nc, hcells]
          exact spec.1
  obtain ⟨c2, h2⟩ := applyLegs_exists c1 t.legs d.legs_nodup legs_pre
  have c2_leg : ∀ leg ∈ t.legs, ∀ pre, c1 leg.cell = some ⟨leg.kind, pre⟩ →
      c2 leg.cell = some ⟨leg.kind, Patch.run pre leg.patch⟩ := by
    intro leg m pre hpre
    obtain ⟨pre', hb, -, hpost⟩ := applyLegs_mem h2 d.legs_nodup leg m
    rw [hpre] at hb
    simp only [Option.bind_some, Cell.storeAt_self, Option.some.injEq] at hb
    subst hb
    exact hpost
  have c2_frame : ∀ c, c ∉ t.legs.map Leg.cell → c2 c = c1 c :=
    fun c hc => applyLegs_frame h2 c hc
  have hcellsOk : applyCells w.cells t = .ok c2 := by
    unfold applyCells
    rw [h1]
    simp only
    rw [h2, hretires]
    rfl
  -- the system half
  have shaped : Shaped t := by
    refine ⟨fun e => d.nonempty ⟨e.1, e.2.1⟩, d.legs_nodup, d.creates_nodup, by simp [hretires]⟩
  have funded' : t.charge ≤ w.meter := by
    intro l
    rw [hcharge]
    unfold chargeOf
    by_cases e : l = .storageBytes
    · subst e
      simp only [if_true]
      exact le_trans d.storage fundedStorage
    · simp only [e, if_false]
      exact funded l e
  have hk : turnCheck H w t height = none := by
    rw [turnCheck_eq_none_iff]
    refine ⟨?_, ⟨by simp [hnb], by simp [hvu]⟩, ?_, ?_, funded'⟩
    · rw [hnull]; exact nodup.map B.key_injective
    · intro n m
      rw [hnull] at m
      obtain ⟨n0, m0, rfl⟩ := List.mem_map.mp m
      exact unspent n0 m0
    · rw [hcharge]; simp [chargeOf, storageOf, patchBytes]
  have hv : Patch.ValidFrom w.system (sysPatch H t height logRoot w.meter) := by
    refine sysPatch_valid_unroomed H (fun c m => (creates_spec c m).1) hretires
      (fun c _ => unretired c.1) (by rw [htx]; exact fresh) hh ⟨?_, ?_⟩ ?_
    · rw [hnull]; exact nodup.map B.key_injective
    · intro n m
      rw [hnull] at m
      obtain ⟨n0, m0, rfl⟩ := List.mem_map.mp m
      exact unspent n0 m0
    · intro l hl
      have pos : 0 < w.meter l := lt_of_lt_of_le (Nat.pos_of_ne_zero hl) (funded' l)
      rw [meter_system] at pos ⊢
      revert pos
      cases w.system ⟨SysSpace.allowance, l⟩ with
      | none => intro pos; exact absurd pos (lt_irrefl 0)
      | some a => intro _; rfl
  have hadmit := admit_of H shaped hh (by rw [htx]; exact fresh) hk hv hcellsOk
  refine ⟨_, (step_eq_some H).2 hadmit, fun c => ?_, rfl⟩
  show c2 c = _
  by_cases hw : c ∈ writeIds intent.writes
  · obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
    obtain ⟨δ, hδ, -, md⟩ := delta_of_write d hw0
    have spec := deltaOf_spec hδ
    cases δ with
    | absent =>
        rw [postCell_written d.writes_nodup hw0 spec.2]
        have nl : w0.cellId.value ∉ t.legs.map Leg.cell := by
          intro m
          obtain ⟨leg, ml, el⟩ := List.mem_map.mp m
          rw [hlegs] at ml
          rcases mem_legsOf.mp ml with ⟨c, mg, cell, -, rfl⟩ | ⟨c, δ', md', hl⟩
          · have e : c = w0.cellId.value := el
            subst e
            exact guardIds_not_written mg hw
          · have e := leg?_cell hl
            rw [el] at e
            subst e
            cases deltas_unique d md md'
            cases hl
        have nc : w0.cellId.value ∉ t.creates.map Prod.fst := by
          intro m'
          obtain ⟨k', s'', m''⟩ := (created_iff _).mp m'
          cases deltas_unique d md m''
        rw [c2_frame _ nl, c1_frame _ nc, hcells]
        exact spec.1
    | create k s' =>
        rw [postCell_written d.writes_nodup hw0 spec.2]
        have ml : (⟨w0.cellId.value, k, B.codec.legPatch k (romPart s') s'⟩ : Leg R) ∈ t.legs := by
          rw [hlegs]; exact mem_legsOf.mpr (.inr ⟨_, _, md, rfl⟩)
        rw [c2_leg _ ml (romPart s') (c1_created _ k s' md), B.codec.legPatch_run]
    | change k s s' =>
        rw [postCell_written d.writes_nodup hw0 spec.2]
        have ml : (⟨w0.cellId.value, k, B.codec.legPatch k s s'⟩ : Leg R) ∈ t.legs := by
          rw [hlegs]; exact mem_legsOf.mpr (.inr ⟨_, _, md, rfl⟩)
        have nc : w0.cellId.value ∉ t.creates.map Prod.fst := by
          intro m'
          obtain ⟨k', s'', m''⟩ := (created_iff _).mp m'
          cases deltas_unique d md m''
        have pre : c1 w0.cellId.value = some ⟨k, s⟩ := by
          rw [c1_frame _ nc, hcells]; exact spec.1
        rw [c2_leg _ ml s pre, B.codec.legPatch_run]
  · rw [postCell_unwritten hw]
    have nc : c ∉ t.creates.map Prod.fst := fun m => hw (created_written c m)
    by_cases hg : c ∈ guardIds intent.writes intent.readGuards
    · have present := d.guards_present c hg
      obtain ⟨cell, hc⟩ := Option.isSome_iff_exists.mp present
      have ml : (⟨c, cell.kind, B.codec.legPatch cell.kind cell.store cell.store⟩ : Leg R) ∈ t.legs := by
        rw [hlegs]; exact mem_legsOf.mpr (.inl ⟨c, hg, cell, hc, rfl⟩)
      have pre : c1 c = some ⟨cell.kind, cell.store⟩ := by
        rw [c1_frame c nc, hcells, hc]
      rw [c2_leg _ ml _ pre, B.codec.legPatch_run, hc]
    · have nl : c ∉ t.legs.map Leg.cell := by
        intro m
        obtain ⟨leg, ml, el⟩ := List.mem_map.mp m
        rw [hlegs] at ml
        rcases mem_legsOf.mp ml with ⟨c', mg, cell, -, rfl⟩ | ⟨c', δ', md', hl⟩
        · have e : c' = c := el
          subst e
          exact hg mg
        · have e := leg?_cell hl
          rw [el] at e
          subst e
          exact hw (deltas_written md')
      rw [c2_frame c nl, c1_frame c nc, hcells]

/-- **`ofIntent_step`**: the world side of `ofIntent_run`.  Under the world
facts the deployed preflight establishes -- a head, a fresh transaction id,
fresh distinct nullifiers, the charge within the meter (the storage lane
against the intent's own storage charge), an empty retired set -- `World.step`
accepts the derived turn, every post cell is the intent's decoded post image
(`postCell`), and the system cell is the turn's system patch. -/
theorem ofIntent_step (B : Bridge R D) (H : History R TransactionId StableEvent D)
    {w : World R TransactionId D} {intent : DataIntent rootBytes} {t : DTurn R D}
    (derived : Turn.ofIntent B H w intent = .ok t)
    {height : Nat} {logRoot : D} (hh : w.head = some (height, logRoot))
    (fresh : w.journal intent.transactionId = none)
    (nodup : intent.nullifiers.Nodup)
    (unspent : ∀ n ∈ intent.nullifiers, w.spent (B.key n) = none)
    (funded : ∀ l, l ≠ .storageBytes → intent.exactCharge l ≤ w.meter l)
    (fundedStorage : intent.exactCharge .storageBytes ≤ w.meter .storageBytes)
    (unretired : ∀ c, w.retired c = none) :
    ∃ w', World.step H w t = some w' ∧
      (∀ c, w'.cells c = postCell B.codec (fun c => w.cells c) intent c) ∧
      w'.system = Patch.run w.system (sysPatch H t height logRoot w.meter) :=
  ofCells_step B H (fun _ => rfl) derived hh fresh nodup unspent funded fundedStorage unretired

omit [DecidableEq D] in
/-- The derived turn's system-facing fields. -/
theorem ofCells_fields {B : Bridge R D} {H : History R TransactionId StableEvent D}
    {cells : CellId → Option (Cell R)} {intent : DataIntent rootBytes} {t : DTurn R D}
    (h : ofCells B H cells intent = .ok t) :
    t.txId = intent.transactionId ∧ t.retires = [] ∧ t.parentRows = [] ∧
      t.nullifiers = intent.nullifiers.map B.key ∧
      (∀ l, l ≠ .storageBytes → t.charge l = intent.exactCharge l) ∧
      t.charge .storageBytes ≤ intent.exactCharge .storageBytes := by
  have d := ofCells_ok h
  have teq := d.eq
  refine ⟨by rw [teq]; rfl, by rw [teq]; rfl, ?_, by rw [teq]; rfl, fun l e => ?_, ?_⟩
  · unfold Turn.parentRows
    rw [List.filterMap_eq_nil_iff]
    intro c m
    rw [teq] at m
    obtain ⟨c', k, s', -, rfl⟩ := mem_createsOf.mp m
    rfl
  · rw [teq]; simp [turnOf, chargeOf, e]
  · have := d.storage
    rw [teq] at this ⊢
    simpa [turnOf, chargeOf, storageOf] using this

end Derive

/-! ## Axiom pins -/

#assert_axioms apply_at_congr
#assert_axioms validFrom_of_distinct
#assert_axioms enabled_of_distinct
#assert_axioms run_of_distinct
#assert_axioms normal_of_distinct
#assert_axioms diff_run
#assert_axioms diff_validFrom_iff
#assert_axioms diff_normal
#assert_axioms diff_valid_iff_executes
#assert_axioms Codec.legPatch_run
#assert_axioms Codec.legPatch_normalize
#assert_axioms Codec.legPatch_valid_iff
#assert_axioms Codec.legPatch_self_valid
#assert_axioms nullifierCode_injective
#assert_axioms digestKey_injective
#assert_axioms ofCells_ok
#assert_axioms ofIntent_minimal
#assert_axioms ofCells_step
#assert_axioms ofIntent_step
#assert_axioms ofCells_fields
#assert_axioms sysCore_unroomed
#assert_axioms sysPatch_valid_unroomed
#assert_axioms applyCreates_exists
#assert_axioms applyLegs_exists


/-! `#print axioms`, pinned: the standard three. -/
/-- info: 'Minidregg.Kernel.TurnOfIntent.diff_valid_iff_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms diff_valid_iff_executes
/-- info: 'Minidregg.Kernel.TurnOfIntent.Codec.legPatch_valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Codec.legPatch_valid_iff
/-- info: 'Minidregg.Kernel.TurnOfIntent.ofIntent_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ofIntent_minimal
/-- info: 'Minidregg.Kernel.TurnOfIntent.ofIntent_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ofIntent_step

end Minidregg.Kernel.TurnOfIntent
