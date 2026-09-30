/-
# Theory.PlanBinding — a plan binds the values at the addresses it reads

DATAMODEL §3.2 / §3.4 / §3.5 / §4.8.  A signed plan used to bind the whole root
of the cell it read.  Every admitted operation writes into the shared authority
cell, so every admission moved that root and invalidated every other agent's
pending plan (lane M8's contention finding).  This module states the binding
that replaces it: a plan names a **footprint** — the addresses it read and the
value it read at each — and admission checks exactly those values against the
current store.

## Shape

* `Footprint L` — a list of `Read`s: an address of the layout and the observed
  value (`none` = absent).  `observe` authors one from a store.
* `admit` — the admission check.  Its only refusal is
  `Refusal.footprintStale a`, naming the first read address whose value moved.
* `rootOf : Store L → Root` — whole-root binding, for comparison
  (`CellState.Materializer.rootOf` is the deployed instance).
* `Opened` — the same footprint as authenticated-map openings, for a verifier
  that holds only roots (`Theory.AuthMap`, two levels).

## Theorems

* `admit_ok_iff`, `admit_refusal_names_stale` — the check and its refusal.
* Poles: `unrelated_write_admits` / `independent_run_admits` (a write outside the
  footprint does not invalidate the plan) and `read_write_refuses` /
  `refusal_names_moved` (a write to a read address does, and the refusal names an
  address that moved).
* `whole_footprint_iff_root` — at the whole cell (`AgreesOn Set.univ`),
  footprint admission is root admission, under the pair carrier `RootBinds`;
  `whole_footprint_admits_root` is the carrier-free direction and
  `root_admits_footprint` shows footprint admission loses nothing.
  `ConstRoot.rootBinds_load_bearing` refutes the carrier at a constant root.
* `footprint_extra_only_disjoint` — whatever footprint admission admits and root
  admission refuses differs from the authored store only outside the footprint.
* `no_toctou` — the values checked are the values used: a patch whose accesses
  lie in an admitted footprint is valid at the current store iff it was valid at
  the authored one, and writes exactly what it would have written there.
* `independent_both_orders`, `independent_commute` — two plans that write
  nothing the other read are both admitted in either order and reach the same
  store.  `Example` runs it on `Store.Example.layout`, with the overlapping pole.
* `Opened.verifyAll_openAll` / `verifyAll_sound` / `twoLevel_sound` — openings
  at the cell root under the world root.  `IdToy.stale_opening_refused` is why
  the *signed* binding is values, not openings: an opening authored at the
  pre-root fails at the next root after a write to a *different* key, so signing
  openings would re-bind the whole root.  `LengthToy.forged_verifies_held_refuses`:
  the length-hash forgery that `verify` accepts is refused by admission against
  the held store.
-/
import Theory.CellState
import Theory.AuthMap

namespace Minidregg.Theory.PlanBinding

open Minidregg.Theory.Store

set_option autoImplicit false

universe u v w y

section Footprints

variable {L : Layout.{u, v, w}}

/-- One read of a plan: an address and the value the plan was authored against
(`none` = the address was absent). -/
structure Read (L : Layout.{u, v, w}) where
  address : Address L
  observed : Option (L.Value address.1)

/-- A plan's read footprint. -/
abbrev Footprint (L : Layout.{u, v, w}) := List (Read L)

/-- The only admission refusal of footprint binding. -/
inductive Refusal (L : Layout.{u, v, w}) where
  | footprintStale (address : Address L)

instance : DecidableEq (Refusal L) := fun
  | .footprintStale x, .footprintStale y =>
      if h : x = y then isTrue (h ▸ rfl)
      else isFalse (fun e => by cases e; exact h rfl)

namespace Footprint

def addresses (fp : Footprint L) : Finset (Address L) := (fp.map Read.address).toFinset

theorem mem_addresses {fp : Footprint L} {a : Address L} :
    a ∈ fp.addresses ↔ ∃ r ∈ fp, r.address = a := by
  simp [addresses]

/-- The footprint's values are the store's values. -/
def Holds (store : Store L) (fp : Footprint L) : Prop :=
  ∀ r ∈ fp, store r.address = r.observed

instance (store : Store L) (fp : Footprint L) : Decidable (Holds store fp) :=
  inferInstanceAs (Decidable (∀ r ∈ fp, store r.address = r.observed))

/-- Author a footprint: read the store at the named addresses. -/
def observe (store : Store L) (as : List (Address L)) : Footprint L :=
  as.map fun a => ⟨a, store a⟩

theorem observe_holds (store : Store L) (as : List (Address L)) :
    Holds store (observe store as) := by
  intro r member
  simp only [observe, List.mem_map] at member
  obtain ⟨a, _, rfl⟩ := member
  rfl

theorem addresses_observe (store : Store L) (as : List (Address L)) :
    (observe store as).addresses = as.toFinset := by
  simp [addresses, observe, Function.comp_def]

/-- The first read whose value the store no longer holds. -/
def firstStale? (store : Store L) : Footprint L → Option (Address L)
  | [] => none
  | r :: rest => if store r.address = r.observed then firstStale? store rest else some r.address

/-- **Admission under footprint binding.** -/
def admit (store : Store L) (fp : Footprint L) : Except (Refusal L) Unit :=
  match firstStale? store fp with
  | none => .ok ()
  | some a => .error (.footprintStale a)

theorem firstStale?_eq_none_iff (store : Store L) (fp : Footprint L) :
    firstStale? store fp = none ↔ Holds store fp := by
  induction fp with
  | nil => simp [firstStale?, Holds]
  | cons r rest ih =>
      unfold firstStale?
      by_cases h : store r.address = r.observed
      · rw [if_pos h, ih]
        constructor
        · intro hrest r' mem
          rcases List.mem_cons.1 mem with rfl | mem
          · exact h
          · exact hrest r' mem
        · intro hall r' mem
          exact hall r' (List.mem_cons_of_mem _ mem)
      · rw [if_neg h]
        simp only [reduceCtorEq, false_iff]
        intro hall
        exact h (hall r List.mem_cons_self)

theorem firstStale?_eq_some {store : Store L} {fp : Footprint L} {a : Address L}
    (h : firstStale? store fp = some a) :
    ∃ r ∈ fp, r.address = a ∧ store r.address ≠ r.observed := by
  induction fp with
  | nil => simp [firstStale?] at h
  | cons r rest ih =>
      unfold firstStale? at h
      by_cases hr : store r.address = r.observed
      · rw [if_pos hr] at h
        obtain ⟨r', mem, eq, ne⟩ := ih h
        exact ⟨r', List.mem_cons_of_mem _ mem, eq, ne⟩
      · rw [if_neg hr] at h
        exact ⟨r, List.mem_cons_self, Option.some.inj h, hr⟩

theorem admit_ok_iff (store : Store L) (fp : Footprint L) :
    admit store fp = .ok () ↔ Holds store fp := by
  rw [← firstStale?_eq_none_iff]
  unfold admit
  split <;> simp_all

/-- Every refusal names a read of the footprint whose value the store no
longer holds. -/
theorem admit_refusal_names_stale {store : Store L} {fp : Footprint L} {a : Address L}
    (h : admit store fp = .error (.footprintStale a)) :
    ∃ r ∈ fp, r.address = a ∧ store r.address ≠ r.observed := by
  unfold admit at h
  split at h
  · cases h
  · rename_i a' stale
    cases h
    exact firstStale?_eq_some stale

/-- Admission is total: it admits or refuses `footprintStale`. -/
theorem admit_cases (store : Store L) (fp : Footprint L) :
    admit store fp = .ok () ∨ ∃ a, admit store fp = .error (.footprintStale a) := by
  unfold admit
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

/-! ### Both poles -/

/-- Two stores that both satisfy a footprint agree on its addresses. -/
theorem agree_of_holds {s₀ s : Store L} {fp : Footprint L}
    (h₀ : Holds s₀ fp) (h : Holds s fp) : ∀ a ∈ fp.addresses, s a = s₀ a := by
  intro a mem
  obtain ⟨r, hr, rfl⟩ := mem_addresses.1 mem
  rw [h r hr, h₀ r hr]

/-- Relative to the authored store, admission is exactly "no read address moved". -/
theorem admit_ok_iff_unmoved {s₀ s : Store L} {fp : Footprint L} (h₀ : Holds s₀ fp) :
    admit s fp = .ok () ↔ ∀ a ∈ fp.addresses, s a = s₀ a := by
  rw [admit_ok_iff]
  constructor
  · exact fun h => agree_of_holds h₀ h
  · intro same r hr
    rw [same r.address (mem_addresses.2 ⟨r, hr, rfl⟩), h₀ r hr]

/-- **Satisfied pole.**  A write outside the footprint does not invalidate it. -/
theorem holds_set_outside {s : Store L} {fp : Footprint L} (h : Holds s fp)
    (a : Address L) (x : Option (L.Value a.1)) (outside : a ∉ fp.addresses) :
    Holds (s.set a x) fp := by
  intro r hr
  have ne : r.address ≠ a := fun e => outside (mem_addresses.2 ⟨r, hr, e⟩)
  rw [Store.set_ne _ _ _ _ ne, h r hr]

theorem unrelated_write_admits {s : Store L} {fp : Footprint L} (h : Holds s fp)
    (a : Address L) (x : Option (L.Value a.1)) (outside : a ∉ fp.addresses) :
    admit (s.set a x) fp = .ok () :=
  (admit_ok_iff _ _).2 (holds_set_outside h a x outside)

/-- The same pole for a whole patch: a patch that writes nothing the footprint
read leaves the footprint admitted. -/
theorem holds_run_disjoint {s : Store L} {fp : Footprint L} (h : Holds s fp)
    (patch : Patch L) (disjoint : Disjoint (Patch.writeFootprint patch) fp.addresses) :
    Holds (Patch.run s patch) fp := by
  intro r hr
  have outside : r.address ∉ Patch.writeFootprint patch := fun w =>
    Finset.disjoint_left.1 disjoint w (mem_addresses.2 ⟨r, hr, rfl⟩)
  rw [Patch.run_frame s patch r.address outside, h r hr]

/-- **Refuted pole.**  A write of a different value to a read address refuses
the plan, and the refusal names an address that moved. -/
theorem read_write_refuses {s : Store L} {fp : Footprint L} (h : Holds s fp)
    {r : Read L} (hr : r ∈ fp) (x : Option (L.Value r.address.1)) (moved : x ≠ r.observed) :
    ∃ a, admit (s.set r.address x) fp = .error (.footprintStale a) ∧
      (s.set r.address x) a ≠ s a := by
  rcases admit_cases (s.set r.address x) fp with ok | ⟨a, refused⟩
  · have := ((admit_ok_iff _ _).1 ok) r hr
    rw [Store.set_eq] at this
    exact absurd this moved
  · refine ⟨a, refused, ?_⟩
    obtain ⟨r', hr', rfl, stale⟩ := admit_refusal_names_stale refused
    rw [h r' hr']
    exact stale

/-- The refusal is exact: it names only a read address that moved since authoring. -/
theorem refusal_names_moved {s₀ s : Store L} {fp : Footprint L} (h₀ : Holds s₀ fp)
    {a : Address L} (refused : admit s fp = .error (.footprintStale a)) :
    a ∈ fp.addresses ∧ s a ≠ s₀ a := by
  obtain ⟨r, hr, rfl, stale⟩ := admit_refusal_names_stale refused
  exact ⟨mem_addresses.2 ⟨r, hr, rfl⟩, by rw [h₀ r hr]; exact stale⟩

end Footprint

/-! ## Footprint binding against whole-root binding -/

section WholeRoot

open Footprint

/-- Two stores agree on a set of addresses. -/
def AgreesOn (A : Set (Address L)) (s₀ s : Store L) : Prop := ∀ a ∈ A, s a = s₀ a

theorem holds_observe_iff (s₀ s : Store L) (as : List (Address L)) :
    Holds s (observe s₀ as) ↔ AgreesOn {a | a ∈ as} s₀ s := by
  constructor
  · intro h a mem
    exact h ⟨a, s₀ a⟩ (List.mem_map.2 ⟨a, mem, rfl⟩)
  · intro h r hr
    simp only [observe, List.mem_map] at hr
    obtain ⟨a, mem, rfl⟩ := hr
    exact h a mem

/-- The whole cell as a footprint: agreement everywhere is equality. -/
theorem agreesOn_univ_iff (s₀ s : Store L) : AgreesOn Set.univ s₀ s ↔ s = s₀ := by
  constructor
  · intro h
    exact DFinsupp.ext fun a => h a (Set.mem_univ a)
  · rintro rfl a _
    rfl

variable {Root : Type y}

/-- The pair carrier of whole-root binding: the root separates this pair of
stores.  It names one pair, so it is not a global injectivity of the root. -/
def RootBinds (rootOf : Store L → Root) (s₀ s : Store L) : Prop :=
  rootOf s = rootOf s₀ → s = s₀

/-- Carrier-free direction: a whole-cell footprint that holds admits under root
binding. -/
theorem whole_footprint_admits_root (rootOf : Store L → Root) {s₀ s : Store L}
    (h : AgreesOn Set.univ s₀ s) : rootOf s = rootOf s₀ := by
  rw [(agreesOn_univ_iff s₀ s).1 h]

/-- **Nothing is lost.**  When the footprint is the whole cell, footprint
admission is root admission (under the pair carrier). -/
theorem whole_footprint_iff_root (rootOf : Store L → Root) {s₀ s : Store L}
    (bind : RootBinds rootOf s₀ s) : AgreesOn Set.univ s₀ s ↔ rootOf s = rootOf s₀ :=
  ⟨whole_footprint_admits_root rootOf, fun same => (agreesOn_univ_iff s₀ s).2 (bind same)⟩

/-- Footprint admission admits everything root admission admits. -/
theorem root_admits_footprint (rootOf : Store L → Root) {s₀ s : Store L} {fp : Footprint L}
    (bind : RootBinds rootOf s₀ s) (same : rootOf s = rootOf s₀) (h₀ : Holds s₀ fp) :
    admit s fp = .ok () := by
  rw [bind same]
  exact (admit_ok_iff _ _).2 h₀

/-- **Strictly more permissive only on disjoint writes.**  A store that footprint
admission admits and root admission refuses differs from the authored store,
and only at addresses outside the footprint. -/
theorem footprint_extra_only_disjoint (rootOf : Store L → Root) {s₀ s : Store L}
    {fp : Footprint L} (h₀ : Holds s₀ fp) (admitted : admit s fp = .ok ())
    (rootRefuses : rootOf s ≠ rootOf s₀) :
    (∃ a, s a ≠ s₀ a) ∧ ∀ a, s a ≠ s₀ a → a ∉ fp.addresses := by
  refine ⟨?_, fun a moved mem => moved ((admit_ok_iff_unmoved h₀).1 admitted a mem)⟩
  by_contra none
  simp only [not_exists, not_not] at none
  exact rootRefuses (by rw [DFinsupp.ext none])

end WholeRoot

/-! ## No TOCTOU: the values checked are the values used -/

section NoToctou

open Footprint

theorem enabled_congr (op : Op L) {s s' : Store L} (same : s op.address = s' op.address) :
    op.Enabled s ↔ op.Enabled s' := by
  cases op <;> simp only [Op.address] at same <;>
    simp only [Op.Enabled, Store.Fresh, same]

theorem apply_agree (op : Op L) {A : Set (Address L)} (mem : op.address ∈ A)
    {s s' : Store L} (same : ∀ a ∈ A, s a = s' a) :
    ∀ a ∈ A, op.apply s a = op.apply s' a := by
  intro a ha
  cases op with
  | read => exact same a ha
  | write space key before after =>
      by_cases e : a = ⟨space, key⟩
      · subst e; simp [Op.apply]
      · simp only [Op.apply]; rw [Store.set_ne _ _ _ _ e, Store.set_ne _ _ _ _ e]; exact same a ha
  | allocate space key value =>
      by_cases e : a = ⟨space, key⟩
      · subst e; simp [Op.apply]
      · simp only [Op.apply]; rw [Store.set_ne _ _ _ _ e, Store.set_ne _ _ _ _ e]; exact same a ha
  | free space key before =>
      by_cases e : a = ⟨space, key⟩
      · subst e; simp [Op.apply]
      · simp only [Op.apply]; rw [Store.set_ne _ _ _ _ e, Store.set_ne _ _ _ _ e]; exact same a ha

/-- A patch's validity and effect on a set containing its accesses depend only
on the store's values on that set. -/
theorem congr_access (patch : Patch L) :
    ∀ (A : Set (Address L)), (↑(Patch.accessFootprint patch) : Set (Address L)) ⊆ A →
      ∀ (s s' : Store L), (∀ a ∈ A, s a = s' a) →
        (Patch.ValidFrom s patch ↔ Patch.ValidFrom s' patch) ∧
          ∀ a ∈ A, Patch.run s patch a = Patch.run s' patch a := by
  induction patch with
  | nil => intro A _ s s' same; exact ⟨Iff.rfl, same⟩
  | cons op rest ih =>
      intro A cover s s' same
      have opMem : op.address ∈ A := cover (by simp [Patch.accessFootprint])
      have restCover : (↑(Patch.accessFootprint rest) : Set (Address L)) ⊆ A := by
        intro a ha
        apply cover
        simp only [Patch.accessFootprint, List.map_cons, List.toFinset_cons, Finset.coe_insert,
          Set.mem_insert_iff, Finset.mem_coe] at ha ⊢
        exact Or.inr ha
      have after := apply_agree op opMem same
      obtain ⟨valid, run⟩ := ih A restCover (op.apply s) (op.apply s') after
      refine ⟨?_, fun a ha => by simpa using run a ha⟩
      simp only [Patch.ValidFrom]
      rw [enabled_congr op (same _ opMem), valid]

/-- **No TOCTOU.**  If the plan's patch accesses only footprint addresses, and
the footprint holds both where the plan was authored (`s₀`) and where it is
admitted (`s`), then the patch is valid at `s` iff it was at `s₀`, it writes at
`s` exactly what it wrote at `s₀`, and every other address keeps `s`'s value. -/
theorem no_toctou {s₀ s : Store L} {fp : Footprint L} (patch : Patch L)
    (cover : Patch.accessFootprint patch ⊆ fp.addresses)
    (h₀ : Holds s₀ fp) (h : Holds s fp) :
    (Patch.ValidFrom s₀ patch ↔ Patch.ValidFrom s patch) ∧
      ∀ a, Patch.run s patch a =
        if a ∈ Patch.writeFootprint patch then Patch.run s₀ patch a else s a := by
  have same : ∀ a ∈ (↑fp.addresses : Set (Address L)), s₀ a = s a :=
    fun a ha => (agree_of_holds h₀ h a ha).symm
  obtain ⟨valid, run⟩ := congr_access patch _ (by exact_mod_cast cover) s₀ s same
  refine ⟨valid, fun a => ?_⟩
  split
  · rename_i written
    exact (run a (cover (Patch.writeFootprint_subset_accessFootprint patch written))).symm
  · rename_i outside
    exact Patch.run_frame s patch a outside

end NoToctou

/-! ## Two plans on disjoint footprints -/

section TwoPlans

open Footprint

/-- A plan: its footprint and the patch it executes, whose accesses the footprint
covers. -/
structure Plan (L : Layout.{u, v, w}) where
  footprint : Footprint L
  patch : Patch L
  covers : Patch.accessFootprint patch ⊆ footprint.addresses

/-- A plan is admitted at a store: its footprint holds and its patch is valid. -/
def Plan.Admits (p : Plan L) (s : Store L) : Prop :=
  Holds s p.footprint ∧ Patch.ValidFrom s p.patch

instance (p : Plan L) (s : Store L) : Decidable (p.Admits s) :=
  inferInstanceAs (Decidable (Holds s p.footprint ∧ Patch.ValidFrom s p.patch))

/-- Neither plan writes an address the other read. -/
def Independent (p q : Plan L) : Prop :=
  Disjoint (Patch.writeFootprint p.patch) q.footprint.addresses ∧
    Disjoint (Patch.writeFootprint q.patch) p.footprint.addresses

instance (p q : Plan L) : Decidable (Independent p q) :=
  inferInstanceAs (Decidable (Disjoint _ _ ∧ Disjoint _ _))

theorem Independent.symm {p q : Plan L} (h : Independent p q) : Independent q p := ⟨h.2, h.1⟩

/-- After an independent plan's patch runs, the other is still admitted
(whatever `p` read: only `p`'s writes can reach `q`). -/
theorem admits_after_independent {p q : Plan L} {s : Store L} (ind : Independent p q)
    (hq : q.Admits s) : q.Admits (Patch.run s p.patch) := by
  have holds := holds_run_disjoint hq.1 p.patch ind.1
  exact ⟨holds, ((no_toctou q.patch q.covers hq.1 holds).1).1 hq.2⟩

/-- **Both orders.**  Two independent plans admitted at one store are each
admitted after the other. -/
theorem independent_both_orders {p q : Plan L} {s : Store L} (ind : Independent p q)
    (hp : p.Admits s) (hq : q.Admits s) :
    q.Admits (Patch.run s p.patch) ∧ p.Admits (Patch.run s q.patch) :=
  ⟨admits_after_independent ind hq, admits_after_independent ind.symm hp⟩

/-- **Commutation.**  Both orders reach the same store. -/
theorem independent_commute {p q : Plan L} {s : Store L} (ind : Independent p q)
    (hp : p.Admits s) (hq : q.Admits s) :
    Patch.run (Patch.run s p.patch) q.patch = Patch.run (Patch.run s q.patch) p.patch := by
  have hpq := holds_run_disjoint hp.1 q.patch ind.2
  have hqp := holds_run_disjoint hq.1 p.patch ind.1
  obtain ⟨_, pAfterQ⟩ := no_toctou p.patch p.covers hp.1 hpq
  obtain ⟨_, qAfterP⟩ := no_toctou q.patch q.covers hq.1 hqp
  apply DFinsupp.ext
  intro a
  rw [qAfterP a, pAfterQ a]
  by_cases wp : a ∈ Patch.writeFootprint p.patch
  · have nq : a ∉ Patch.writeFootprint q.patch := fun wq =>
      Finset.disjoint_left.1 ind.1 wp (q.covers (Patch.writeFootprint_subset_accessFootprint _ wq))
    rw [if_neg nq, if_pos wp]
  · rw [if_neg wp]
    by_cases wq : a ∈ Patch.writeFootprint q.patch
    · rw [if_pos wq]
    · rw [if_neg wq, Patch.run_frame s p.patch a wp, Patch.run_frame s q.patch a wq]

/-- **Overlap pole.**  If one plan changes a value the other read, the other is
refused `footprintStale`, naming an address that moved. -/
theorem overlap_refused {p q : Plan L} {s : Store L} (hp : p.Admits s)
    {a : Address L} (read : a ∈ p.footprint.addresses)
    (moved : Patch.run s q.patch a ≠ s a) :
    ∃ b, admit (Patch.run s q.patch) p.footprint = .error (.footprintStale b) ∧
      b ∈ p.footprint.addresses ∧ Patch.run s q.patch b ≠ s b := by
  rcases admit_cases (Patch.run s q.patch) p.footprint with ok | ⟨b, refused⟩
  · exact absurd ((admit_ok_iff_unmoved hp.1).1 ok a read) moved
  · exact ⟨b, refused, refusal_names_moved hp.1 refused⟩

end TwoPlans

end Footprints

/-! ## Worked instance: two agents on `Store.Example.layout` -/

namespace Example

open Store.Example
open Footprint

/-- Agent A owns `heap[1]`, agent B owns `heap[2]`; a third plan reads `heap[1]`. -/
def start : Store layout :=
  (empty.set (at_ .heap 1) (some (10 : Nat))).set (at_ .heap 2) (some (20 : Nat))

def fpA : Footprint layout := [⟨at_ .heap 1, some (10 : Nat)⟩]
def fpB : Footprint layout := [⟨at_ .heap 2, some (20 : Nat)⟩]

def planA : Plan layout := ⟨fpA, [write .heap 1 10 11], by decide⟩
def planB : Plan layout := ⟨fpB, [write .heap 2 20 21], by decide⟩

/-- A plan that read agent A's address and writes a third one. -/
def fpC : Footprint layout := [⟨at_ .heap 1, some (10 : Nat)⟩, ⟨at_ .heap 3, none⟩]

def planC : Plan layout := ⟨fpC, [read .heap 1 (some 10), allocate .heap 3 1], by decide⟩

theorem planA_admits : planA.Admits start := by decide
theorem planB_admits : planB.Admits start := by decide

theorem independent_AB : Independent planA planB := by decide

/-- Both orders admitted, the same store reached. -/
theorem two_agents_disjoint :
    planB.Admits (Patch.run start planA.patch) ∧ planA.Admits (Patch.run start planB.patch) ∧
      Patch.run (Patch.run start planA.patch) planB.patch =
        Patch.run (Patch.run start planB.patch) planA.patch :=
  ⟨(independent_both_orders independent_AB planA_admits planB_admits).1,
    (independent_both_orders independent_AB planA_admits planB_admits).2,
    independent_commute independent_AB planA_admits planB_admits⟩

/-- The same two admissions, computed by the checker in both orders. -/
theorem two_agents_disjoint_computed :
    admit (Patch.run start planA.patch) planB.footprint = .ok () ∧
      admit (Patch.run start planB.patch) planA.footprint = .ok () := by
  decide

/-- Overlapping: after A commits, C (which read `heap[1] = 10`) is refused
`footprintStale heap[1]`. -/
theorem overlap_refused_computed :
    admit (Patch.run start planA.patch) planC.footprint =
      .error (.footprintStale (at_ .heap 1)) := by
  decide

/-- …while under whole-root binding even B, which A never touched, is refused
(any root that separates these two stores refuses it). -/
theorem whole_root_refuses_B :
    Patch.run start planA.patch ≠ start := by
  intro h
  have := congrArg (fun s : Store layout => s (at_ .heap 1)) h
  revert this
  decide

end Example

/-! ## The carrier of whole-root binding is load-bearing -/

namespace ConstRoot

open Store.Example

/-- At a constant root, root admission accepts a store that moved; the
whole-cell footprint refuses it.  So `whole_footprint_iff_root` needs its
carrier. -/
theorem rootBinds_load_bearing :
    (fun _ : Store layout => ()) (empty.set (at_ .heap 7) (some (1 : Nat))) =
        (fun _ : Store layout => ()) empty ∧
      ¬ AgreesOn Set.univ empty (empty.set (at_ .heap 7) (some (1 : Nat))) := by
  refine ⟨rfl, fun h => ?_⟩
  have := h (at_ .heap 7) (Set.mem_univ _)
  revert this
  decide

end ConstRoot

/-! ## Openings: the footprint for a verifier that holds only roots -/

namespace Opened

open Minidregg.Theory.AuthMap

section

variable {K V D : Type} [DecidableEq K] [DecidableEq D] (S : Scheme K V D)

/-- One opened read: a key, the claimed value, its opening. -/
structure Entry (K V D : Type) where
  key : K
  value : Option V
  opening : Scheme.Opening K V D

/-- A verifier holding only the root checks every opening. -/
def verifyAll (r : D) (fp : List (Entry K V D)) : Bool :=
  fp.all fun e => S.verify r e.key e.value e.opening

/-- The observation side: open the named keys of a held map. -/
def openAll (m : Map K V) (keys : List K) : List (Entry K V D) :=
  keys.map fun k => ⟨k, lookup S.ix m k, S.opening m k⟩

/-- The admission side for a party that holds the map: compare values. -/
def firstStaleHeld? [DecidableEq V] (m : Map K V) : List (Entry K V D) → Option K
  | [] => none
  | e :: rest => if lookup S.ix m e.key = e.value then firstStaleHeld? m rest else some e.key

theorem verifyAll_openAll (m : Map K V) (keys : List K) :
    verifyAll S (S.root m) (openAll S m keys) = true := by
  simp [verifyAll, openAll, S.verify_opening]

theorem verifyAll_sound (m : Map K V) (fp : List (Entry K V D))
    (bind : ∀ e ∈ fp, S.PathBinding m e.key e.value e.opening)
    (h : verifyAll S (S.root m) fp = true) :
    ∀ e ∈ fp, lookup S.ix m e.key = e.value := by
  intro e he
  simp only [verifyAll, List.all_eq_true] at h
  exact (S.verify_sound m e.key e.value e.opening (bind e he) (h e he)).symm

end

/-- **Two levels.**  A world opening of the cell root and cell openings of the
footprint, each under its carrier, prove that the cell is present and holds the
footprint's values. -/
theorem twoLevel_sound {I A X E D : Type} [DecidableEq I] [DecidableEq A] [DecidableEq E]
    [DecidableEq D] (Cs : Scheme A X E) (W : Scheme I E D)
    (w : Map I (Map A X)) (c : I) (r : E) (πw : Scheme.Opening I E D)
    (fp : List (Entry A X E))
    (hbw : W.PathBinding (worldSlots Cs.root w) c (some r) πw)
    (hw : W.verify (worldRoot W Cs.root w) c (some r) πw = true)
    (hbc : ∀ cell, lookup W.ix w c = some cell → ∀ e ∈ fp, Cs.PathBinding cell e.key e.value e.opening)
    (hc : verifyAll Cs r fp = true) :
    ∃ cell, lookup W.ix w c = some cell ∧ ∀ e ∈ fp, lookup Cs.ix cell e.key = e.value := by
  obtain ⟨cell, hl, hr⟩ := world_sound W Cs.root w c r πw hbw hw
  subst hr
  exact ⟨cell, hl, verifyAll_sound Cs cell fp (hbc cell hl) hc⟩

/-- Two-level completeness: the honest world opening and the honest cell
openings verify. -/
theorem twoLevel_complete {I A X E D : Type} [DecidableEq I] [DecidableEq A] [DecidableEq E]
    [DecidableEq D] (Cs : Scheme A X E) (W : Scheme I E D)
    (w : Map I (Map A X)) (c : I) (cell : Map A X) (hl : lookup W.ix w c = some cell)
    (keys : List A) :
    W.verify (worldRoot W Cs.root w) c (some (Cs.root cell))
        (W.opening (worldSlots Cs.root w) c) = true ∧
      verifyAll Cs (Cs.root cell) (openAll Cs cell keys) = true :=
  ⟨by simpa [hl] using world_opening W Cs.root w c, verifyAll_openAll Cs cell keys⟩

/-! ### Why the signed binding is values, not openings -/

namespace IdToy

open Minidregg.Theory.AuthMap.IdToy

/-- Key 2 moves; key 1 does not. -/
def moved : Map (Fin 4) UInt8 := write IdToy.ix IdToy.m 2 (some 5)

/-- **An opening binds the root.**  Key 1 still holds 7 after a write to key 2,
but the opening authored before the write no longer verifies at the new root;
the one re-opened at the new root does.  A header that signed openings would be
invalidated by every write to the cell, which is the contention this module
removes. -/
theorem stale_opening_refused :
    lookup IdToy.ix moved 1 = some 7 ∧
      scheme.verify (scheme.root moved) 1 (some 7) (scheme.opening IdToy.m 1) = false ∧
        scheme.verify (scheme.root moved) 1 (some 7) (scheme.opening moved 1) = true := by
  decide

end IdToy

namespace LengthToy

open Minidregg.Theory.AuthMap.LengthToy

/-- **A forged opening.**  At the 8-bit length hash the forged opening of
`5 ↦ 8` verifies at the root (the carrier's refuted pole), and admission against
the held map refuses it, naming key 5. -/
theorem forged_verifies_held_refuses :
    verifyAll scheme (scheme.root LengthToy.m) [⟨5, some 8, forged⟩] = true ∧
      firstStaleHeld? scheme LengthToy.m [⟨5, some 8, forged⟩] = some 5 := by
  decide

end LengthToy

end Opened

/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.PlanBinding.Footprint.admit_ok_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Footprint.admit_ok_iff
/-- info: 'Minidregg.Theory.PlanBinding.Footprint.admit_refusal_names_stale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Footprint.admit_refusal_names_stale
/-- info: 'Minidregg.Theory.PlanBinding.Footprint.unrelated_write_admits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Footprint.unrelated_write_admits
/-- info: 'Minidregg.Theory.PlanBinding.Footprint.read_write_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Footprint.read_write_refuses
/-- info: 'Minidregg.Theory.PlanBinding.Footprint.refusal_names_moved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Footprint.refusal_names_moved
/-- info: 'Minidregg.Theory.PlanBinding.whole_footprint_iff_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whole_footprint_iff_root
/-- info: 'Minidregg.Theory.PlanBinding.root_admits_footprint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms root_admits_footprint
/-- info: 'Minidregg.Theory.PlanBinding.footprint_extra_only_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms footprint_extra_only_disjoint
/-- info: 'Minidregg.Theory.PlanBinding.no_toctou' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_toctou
/-- info: 'Minidregg.Theory.PlanBinding.independent_both_orders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms independent_both_orders
/-- info: 'Minidregg.Theory.PlanBinding.independent_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms independent_commute
/-- info: 'Minidregg.Theory.PlanBinding.overlap_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms overlap_refused
/-- info: 'Minidregg.Theory.PlanBinding.Example.two_agents_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.two_agents_disjoint
/-- info: 'Minidregg.Theory.PlanBinding.Example.two_agents_disjoint_computed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.two_agents_disjoint_computed
/-- info: 'Minidregg.Theory.PlanBinding.Example.overlap_refused_computed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.overlap_refused_computed
/-- info: 'Minidregg.Theory.PlanBinding.Example.whole_root_refuses_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.whole_root_refuses_B
/-- info: 'Minidregg.Theory.PlanBinding.ConstRoot.rootBinds_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ConstRoot.rootBinds_load_bearing
/-- info: 'Minidregg.Theory.PlanBinding.Opened.verifyAll_openAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Opened.verifyAll_openAll
/-- info: 'Minidregg.Theory.PlanBinding.Opened.verifyAll_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Opened.verifyAll_sound
/-- info: 'Minidregg.Theory.PlanBinding.Opened.twoLevel_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Opened.twoLevel_sound
/-- info: 'Minidregg.Theory.PlanBinding.Opened.twoLevel_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Opened.twoLevel_complete
/-- info: 'Minidregg.Theory.PlanBinding.Opened.IdToy.stale_opening_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Opened.IdToy.stale_opening_refused
/-- info: 'Minidregg.Theory.PlanBinding.Opened.LengthToy.forged_verifies_held_refuses' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Opened.LengthToy.forged_verifies_held_refuses

end Minidregg.Theory.PlanBinding
