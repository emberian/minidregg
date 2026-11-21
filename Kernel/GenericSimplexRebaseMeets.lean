import Kernel.GenericSimplexRebaseGhost
import Kernel.GenericSimplexTip

/-! `rebase` meets `Rebased`.

`GenericSimplexRelative.rebase` maps every kept view; when that succeeds, the state it
leaves, given the audit `ghost_rebase` asks for (`ghostAfter`), is `Rebased`. Nothing here
is about the model: that the floor view's block is the tip is what the map itself checks
(it yields nothing otherwise, and the replica halts), and that the floor view is there to
be checked is `tipped_floor`. When the map fails the replica halts with its state as it
was, and there is nothing to show. -/
namespace Minidregg.Kernel.GenericSimplexRebaseMeets
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexRelative
open Minidregg.Kernel.GenericSimplexCausal
open Minidregg.Kernel.GenericSimplexFloor
open Minidregg.Kernel.GenericSimplexTip
open Minidregg.Kernel.GenericSimplexRebaseGhost
set_option autoImplicit false

/-- What `rebase` does to one kept view. -/
def rebaseKept (c : Config) (self floor : Nat) (tip : Block) (v : View) : Option View :=
  if v.number ≤ floor then
    if v.committed == some tip then
      some { number := v.number, prepared := [[]], committed := some [], disabled := v.disabled }
    else none
  else rebaseView c self tip v

/-- The specification state after a rebase: the rebased views, nothing delivered, and the
old audit read from the new origin behind the floor view's parent. -/
def ghostAfter (G : State) (views : List View) (checked : List Block) : State :=
  { G with
    views := views, checked := checked, committedTip := [], delivered := []
    audit := .prepare G.self G.lastCommitted [] ::
      G.audit.filterMap (rebaseEvent G.lastCommitted G.committedTip) }

theorem mapM_map {α β γ : Type} (f : α → Option β) (g : α → γ) (g' : β → γ)
    (keeps : ∀ x y, f x = some y → g' y = g x) : ∀ (items : List α) (out : List β),
    items.mapM f = some out → out.map g' = items.map g := by
  intro items
  induction items with
  | nil => intro out same; simp at same; subst same; rfl
  | cons head rest ih =>
    intro out same
    rw [List.mapM_cons] at same
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at same
    obtain ⟨image, named, images, restNamed, rfl⟩ := same
    rw [List.map_cons, List.map_cons, keeps head image named, ih images restNamed]

theorem rebaseKept_number {c : Config} {self floor : Nat} {tip : Block} {v rv : View}
    (same : rebaseKept c self floor tip v = some rv) : rv.number = v.number := by
  unfold rebaseKept at same
  split at same
  · split at same
    · cases same; rfl
    · cases same
  · exact (rebaseView_fields same).1

theorem viewAt_absent (s : State) (n : Nat) (absent : ∀ v ∈ s.views, v.number ≠ n) :
    viewAt s n = { number := n } := by
  unfold viewAt
  have none : s.views.find? (fun v => v.number == n) = none := by
    rw [List.find?_eq_none]
    intro v member
    simpa using absent v member
  rw [none]
  rfl

theorem rebaseView_empty (c : Config) (self n : Nat) (tip : Block) :
    rebaseView c self tip { number := n } = some { number := n } := rfl

/-- **`rebase` meets `Rebased`**, when its map over the kept views succeeds. Also: the new
state keeps only views at or above the floor, and the two floor facts hold of it again. -/
theorem rebased_meets {c : Config} {G : State} {views : List View} (checked : List Block)
    (unique : ViewsUnique G) (floorInv : FloorInvariant G) (tipped : Tipped G)
    (nonempty : G.committedTip ≠ [])
    (mapped : (G.views.filter fun v => G.lastCommitted ≤ v.number).mapM
      (rebaseKept c G.self G.lastCommitted G.committedTip) = some views) :
    Rebased c G.committedTip G (ghostAfter G views checked) ∧
      (∀ v ∈ views, G.lastCommitted ≤ v.number) ∧
      FloorInvariant (ghostAfter G views checked) ∧ Tipped (ghostAfter G views checked) := by
  have numbers := mapM_map _ View.number View.number
    (fun x y same => rebaseKept_number same) _ _ mapped
  have live : ∀ v ∈ views, G.lastCommitted ≤ v.number := by
    intro v member
    obtain ⟨x, inside, maps⟩ := mapM_out _ _ _ mapped v member
    rw [rebaseKept_number maps]
    exact of_decide_eq_true (List.mem_filter.mp inside).2
  have unique' : ViewsUnique (ghostAfter G views checked) := by
    show (views.map View.number).Nodup
    rw [numbers]
    exact unique.sublist (List.Sublist.map _ List.filter_sublist)
  have at_ : ∀ v ∈ views, viewAt (ghostAfter G views checked) v.number = v :=
    fun v member => viewAt_member _ v unique' member
  have source : ∀ v ∈ views, ∃ w ∈ G.views, w.number = v.number := by
    intro v member
    obtain ⟨x, inside, maps⟩ := mapM_out _ _ _ mapped v member
    exact ⟨x, (List.mem_filter.mp inside).1, (rebaseKept_number maps).symm⟩
  have image : ∀ v ∈ G.views, G.lastCommitted ≤ v.number →
      ∃ y ∈ views, rebaseKept c G.self G.lastCommitted G.committedTip v = some y := by
    intro v member kept
    exact mapM_in _ _ _ mapped v (List.mem_filter.mpr ⟨member, decide_eq_true kept⟩)
  have above : ∀ n, G.lastCommitted < n →
      rebaseView c G.self G.committedTip (viewAt G n) = some (viewAt (ghostAfter G views checked) n) := by
    intro n high
    by_cases present : ∃ v ∈ G.views, v.number = n
    · obtain ⟨v, member, rfl⟩ := present
      obtain ⟨y, inside, maps⟩ := image v member (Nat.le_of_lt high)
      rw [viewAt_member G v unique member, ← rebaseKept_number maps, at_ y inside, ← maps]
      unfold rebaseKept
      rw [ite_eq_right (by omega)]
    · have absent : ∀ v ∈ G.views, v.number ≠ n := fun v member same => present ⟨v, member, same⟩
      have absent' : ∀ v ∈ (ghostAfter G views checked).views, v.number ≠ n := by
        intro v member same
        obtain ⟨w, inside, named⟩ := source v member
        exact absent w inside (named.trans same)
      rw [viewAt_absent G n absent, viewAt_absent _ n absent']
      exact rebaseView_empty c G.self n G.committedTip
  have reached := tipped_floor tipped floorInv nonempty
  obtain ⟨v, member, _, named⟩ := committed_member G G.lastCommitted reached
  obtain ⟨y, inside, maps⟩ := image v member (Nat.le_of_eq named.symm)
  have whole : viewAt G G.lastCommitted = v := named ▸ viewAt_member G v unique member
  have floorView : (viewAt G G.lastCommitted).committed = some G.committedTip ∧
      viewAt (ghostAfter G views checked) G.lastCommitted =
        { number := G.lastCommitted, prepared := [[]], committed := some [],
          disabled := (viewAt G G.lastCommitted).disabled } := by
    have yNumber := rebaseKept_number maps
    unfold rebaseKept at maps
    simp only [Nat.le_of_eq named, ite_true] at maps
    split at maps
    · rename_i same
      cases maps
      refine ⟨by rw [whole]; exact beq_iff_eq.mp same, ?_⟩
      have located := at_ _ inside
      simp only [named] at located
      rw [located, whole]
    · cases maps
  have below : ∀ n, n < G.lastCommitted → viewAt (ghostAfter G views checked) n = { number := n } := by
    intro n low
    apply viewAt_absent
    intro w inside same
    have := live w inside
    omega
  refine ⟨?_, live, ?_, Or.inl rfl⟩
  · exact
      { self := rfl, current := rfl, floor := rfl, evidence := rfl, delivered := rfl, audit := rfl
        unique := unique'
        named := fun w inside => ⟨(at_ w inside).symm, source w inside⟩
        above := above
        floorView := floorView
        below := below }
  · constructor
    · intro n flag
      show n ≤ G.lastCommitted
      by_contra high
      have moved := (rebaseView_fields (above n (by omega))).2.2.2.2.1
      have none : (viewAt G n).committed = none := by
        cases found : (viewAt G n).committed with
        | none => rfl
        | some block =>
          have := floorInv.bound n (by rw [found]; rfl)
          omega
      rw [none] at moved
      simp only [stripOption, Option.some.injEq] at moved
      rw [← moved] at flag
      cases flag
    · right
      show (viewAt (ghostAfter G views checked) G.lastCommitted).committed.isSome = true
      rw [floorView.2]
      rfl

#assert_axioms rebased_meets

end Minidregg.Kernel.GenericSimplexRebaseMeets
