/-
# `Assurance/LightClientAndViewLens.lean`

Lean `v4.35.0` assurance module for the Wave-8 `deos-view` and `eth-lightclient` /
`cosmos-lightclient` quarry blueprints (`Phase 1` `obend-surfaces` & `obend-lightclients`):
- **Part A:** Complete toolkit-free 25-variant `ViewNode` IR (`deos-view/src/tree.rs:25-249`),
  cut `Disposition` (`sever / attenuate / interpose / tether`, `FrustumMembrane.lean:661`),
  **Fog-of-War Observer Non-Interference**, deterministic tree **diff/patch roundtrip**
  (`applyPatch v (diff v v') = some v'`), and **`synthesizeRepairBadge`** (`Affordance.lean:235`).
- **Part B:** **`S11`-Hardened Electra (`≥ 342/512`, mainnet `397/512`) & CometBFT (`> 2/3`)
  Header Gates** enforcing `expectedChainId`, `attestedSlot ≤ signatureSlot`, slot-derived
  sync-committee period (`slot / 8192`), `hostNow ≤ attestedTime + maxStaleness`, clock-drift
  bounds, domain-separated `forkDigest`, and non-decreasing finalized height, with universal
  refusal theorems, `#tooth` falsifiers, and golden witnesses shared with Rust `quarried_shells`.
-/

namespace Minidregg.Assurance.LightClientAndViewLens

set_option autoImplicit false

/-! ## Part A: 25-Variant `ViewNode` IR, `Frustum` Non-Interference & Diff/Patch -/

abbrev CellId := String

inductive BindFmt where | raw | hex | id | amount deriving DecidableEq, Repr
inductive Disclosure where | simple | adept deriving DecidableEq, Repr

structure PillCase where
  value : Nat
  label : String
  tag : String
  deriving DecidableEq, Repr

structure Crumb where
  label : String
  turn : String
  arg : Int
  deriving DecidableEq, Repr

structure MenuItem where
  label : String
  turn : String
  arg : Int
  enabled : Bool
  wantsText : Bool
  deriving DecidableEq, Repr

structure HaloHandle where
  glyph : String
  turn : String
  arg : Int
  enabled : Bool
  deriving DecidableEq, Repr

structure CoordCell where
  glyph : String
  tag : String
  turn : String
  arg : Int
  highlight : Bool
  deriving DecidableEq, Repr

inductive HostStatus where
  | live
  | severed (snapshotDigest : Nat)
  | attenuated (allowedCount : Nat)
  | interposed (mockLabel : String)
  deriving DecidableEq, Repr

mutual
  /-- Complete 25-variant toolkit-free `ViewNode` IR (`deos-view/src/tree.rs:25-249`).
  `sectionBox` mirrors Rust `ViewNode::Section` (`section` is a Lean keyword). -/
  inductive ViewNode where
    | vstack (children : ViewList)
    | row (children : ViewList)
    | text (body : String)
    | bind (slot : Nat) (label : String) (fmt : BindFmt) (resolved : Option Nat)
    | button (label turn : String) (arg : Int)
    | input (bindView fireTurn submitLabel : String)
    | list (items : ViewList)
    | table (rows : ViewList)
    | sectionBox (title tag : String) (children : ViewList)
    | tabs (labels : List String) (selectedSlot : Nat) (selectTurn : String)
        (resolvedActive : Option Nat) (panels : ViewList)
    | gauge (slot maxVal : Nat) (label : String) (resolved : Option Nat)
    | divider
    | host (cell : CellId) (status : HostStatus) (view : ViewOpt)
    | grid (cols : Nat) (children : ViewList)
    | breadcrumb (items : List Crumb)
    | progress (value maxVal : Nat) (label : String)
    | pill (label tag : String) (slot : Option Nat) (cases : List PillCase) (resolved : Option Nat)
    | icon (glyph tag : String)
    | menu (items : List MenuItem)
    | halo (targetSlot : Nat) (handles : List HaloHandle)
    | slider (slot minVal maxVal : Nat) (turn : String) (resolved : Option Nat)
    | toggle (slot : Nat) (onTurn offTurn glyphOn glyphOff label : String) (resolved : Option Nat)
    | tile (handle : String) (w h : Nat)
    | coordGrid (cols : Nat) (cells : List CoordCell)
    | adept (inner : ViewNode)
    deriving DecidableEq, Repr

  inductive ViewList where
    | nil
    | cons (hd : ViewNode) (tl : ViewList)
    deriving DecidableEq, Repr

  inductive ViewOpt where
    | none
    | some (node : ViewNode)
    deriving DecidableEq, Repr
end

def ViewList.length : ViewList → Nat
  | .nil => 0
  | .cons _ tl => 1 + tl.length

/-- Cut disposition for hosted cells (`Obend/Vault/FrustumMembrane.lean:661`). -/
inductive Disposition where
  | sever (snapshotDigest : Nat)
  | attenuate (allowedSlots : List (CellId × Nat))
  | interpose (mockLabel : String)
  | tether
  deriving DecidableEq, Repr

structure Frustum where
  viewer : CellId
  visibleSlots : List (CellId × Nat)
  policy : CellId → Disposition

def Frustum.restrict (f : Frustum) (allowed : List (CellId × Nat)) : Frustum :=
  { f with visibleSlots := f.visibleSlots.filter (fun p => allowed.contains p) }

abbrev WorldState := CellId → Nat → Nat

def AgreesOnVisible (f : Frustum) (s₁ s₂ : WorldState) : Prop :=
  ∀ c k, (c, k) ∈ f.visibleSlots → s₁ c k = s₂ c k

theorem agreesOnVisible_restrict {f : Frustum} {allowed : List (CellId × Nat)}
    {s₁ s₂ : WorldState} (h : AgreesOnVisible f s₁ s₂) :
    AgreesOnVisible (f.restrict allowed) s₁ s₂ := by
  intro c k hmem; exact h c k (List.mem_filter.mp hmem).1

def readVisibleSlot (f : Frustum) (s : WorldState) (cell : CellId) (slot : Nat) : Option Nat :=
  if f.visibleSlots.contains (cell, slot) then some (s cell slot) else none

theorem readVisibleSlot_eq_of_agrees {f : Frustum} {s₁ s₂ : WorldState}
    (h : AgreesOnVisible f s₁ s₂) (cell : CellId) (slot : Nat) :
    readVisibleSlot f s₁ cell slot = readVisibleSlot f s₂ cell slot := by
  unfold readVisibleSlot
  cases hc : f.visibleSlots.contains (cell, slot) with
  | false => rfl
  | true => simp [h cell slot (List.mem_of_elem_eq_true hc)]

mutual
  def projectViewNode (f : Frustum) (s : WorldState) (cur : CellId) : ViewNode → ViewNode
    | .vstack cs => .vstack (projectViewList f s cur cs)
    | .row cs => .row (projectViewList f s cur cs)
    | .text body => .text body
    | .bind slot lbl fmt _ => .bind slot lbl fmt (readVisibleSlot f s cur slot)
    | .button lbl turn arg => .button lbl turn arg
    | .input bv ft sl => .input bv ft sl
    | .list cs => .list (projectViewList f s cur cs)
    | .table rs => .table (projectViewList f s cur rs)
    | .sectionBox title tag cs => .sectionBox title tag (projectViewList f s cur cs)
    | .tabs lbls sel turn _ ps =>
      .tabs lbls sel turn (readVisibleSlot f s cur sel) (projectViewList f s cur ps)
    | .gauge slot maxV lbl _ => .gauge slot maxV lbl (readVisibleSlot f s cur slot)
    | .divider => .divider
    | .host cell _ sub =>
      match f.policy cell with
      | .sever digest => .host cell (.severed digest) .none
      | .attenuate allowed =>
        let f' := f.restrict allowed
        .host cell (.attenuated f'.visibleSlots.length) (projectViewOpt f' s cell sub)
      | .interpose mock => .host cell (.interposed mock) .none
      | .tether => .host cell .live (projectViewOpt f s cell sub)
    | .grid cols cs => .grid cols (projectViewList f s cur cs)
    | .breadcrumb items => .breadcrumb items
    | .progress v m lbl => .progress v m lbl
    | .pill lbl tag oslot cases _ =>
      let r := match oslot with | some sl => readVisibleSlot f s cur sl | none => none
      .pill lbl tag oslot cases r
    | .icon g t => .icon g t
    | .menu items => .menu items
    | .halo ts hs => .halo ts hs
    | .slider sl mn mx turn _ => .slider sl mn mx turn (readVisibleSlot f s cur sl)
    | .toggle sl onT offT gOn gOff lbl _ =>
      .toggle sl onT offT gOn gOff lbl (readVisibleSlot f s cur sl)
    | .tile h w ht => .tile h w ht
    | .coordGrid cols cs => .coordGrid cols cs
    | .adept inner => .adept (projectViewNode f s cur inner)

  def projectViewList (f : Frustum) (s : WorldState) (cur : CellId) : ViewList → ViewList
    | .nil => .nil
    | .cons hd tl => .cons (projectViewNode f s cur hd) (projectViewList f s cur tl)

  def projectViewOpt (f : Frustum) (s : WorldState) (cur : CellId) : ViewOpt → ViewOpt
    | .none => .none
    | .some n => .some (projectViewNode f s cur n)
end

mutual
  /-- **Fog-of-War Observer Non-Interference**: agreeing on `frustum.visibleSlots` yields
  identical projected 25-variant `ViewNode` trees regardless of secret mutations. -/
  theorem fog_of_war_viewNode_noninterference :
      ∀ (v : ViewNode) (f : Frustum) (s₁ s₂ : WorldState) (cur : CellId),
        AgreesOnVisible f s₁ s₂ →
        projectViewNode f s₁ cur v = projectViewNode f s₂ cur v
    | .vstack cs, f, s₁, s₂, cur, h => by
      simp only [projectViewNode, fog_of_war_viewList_noninterference cs f s₁ s₂ cur h]
    | .row cs, f, s₁, s₂, cur, h => by
      simp only [projectViewNode, fog_of_war_viewList_noninterference cs f s₁ s₂ cur h]
    | .text _, _, _, _, _, _ => rfl
    | .bind slot _ _ _, f, s₁, s₂, cur, h => by
      simp only [projectViewNode, readVisibleSlot_eq_of_agrees h cur slot]
    | .button _ _ _, _, _, _, _, _ => rfl
    | .input _ _ _, _, _, _, _, _ => rfl
    | .list cs, f, s₁, s₂, cur, h => by
      simp only [projectViewNode, fog_of_war_viewList_noninterference cs f s₁ s₂ cur h]
    | .table rs, f, s₁, s₂, cur, h => by
      simp only [projectViewNode, fog_of_war_viewList_noninterference rs f s₁ s₂ cur h]
    | .sectionBox _ _ cs, f, s₁, s₂, cur, h => by
      simp only [projectViewNode, fog_of_war_viewList_noninterference cs f s₁ s₂ cur h]
    | .tabs _ sel _ _ ps, f, s₁, s₂, cur, h => by
      simp only [projectViewNode, readVisibleSlot_eq_of_agrees h cur sel,
        fog_of_war_viewList_noninterference ps f s₁ s₂ cur h]
    | .gauge slot _ _ _, f, s₁, s₂, cur, h => by
      simp only [projectViewNode, readVisibleSlot_eq_of_agrees h cur slot]
    | .divider, _, _, _, _, _ => rfl
    | .host cell _ sub, f, s₁, s₂, cur, h => by
      simp only [projectViewNode]
      cases f.policy cell with
      | sever _ => rfl
      | interpose _ => rfl
      | attenuate allowed =>
        simp only [fog_of_war_viewOpt_noninterference sub (f.restrict allowed) s₁ s₂ cell
          (agreesOnVisible_restrict h)]
      | tether =>
        simp only [fog_of_war_viewOpt_noninterference sub f s₁ s₂ cell h]
    | .grid _ cs, f, s₁, s₂, cur, h => by
      simp only [projectViewNode, fog_of_war_viewList_noninterference cs f s₁ s₂ cur h]
    | .breadcrumb _, _, _, _, _, _ => rfl
    | .progress _ _ _, _, _, _, _, _ => rfl
    | .pill _ _ oslot _ _, f, s₁, s₂, cur, h => by
      simp only [projectViewNode]
      cases oslot with | none => rfl | some sl => simp only [readVisibleSlot_eq_of_agrees h cur sl]
    | .icon _ _, _, _, _, _, _ => rfl
    | .menu _, _, _, _, _, _ => rfl
    | .halo _ _, _, _, _, _, _ => rfl
    | .slider sl _ _ _ _, f, s₁, s₂, cur, h => by
      simp only [projectViewNode, readVisibleSlot_eq_of_agrees h cur sl]
    | .toggle sl _ _ _ _ _ _, f, s₁, s₂, cur, h => by
      simp only [projectViewNode, readVisibleSlot_eq_of_agrees h cur sl]
    | .tile _ _ _, _, _, _, _, _ => rfl
    | .coordGrid _ _, _, _, _, _, _ => rfl
    | .adept inner, f, s₁, s₂, cur, h => by
      simp only [projectViewNode, fog_of_war_viewNode_noninterference inner f s₁ s₂ cur h]

  theorem fog_of_war_viewList_noninterference :
      ∀ (vs : ViewList) (f : Frustum) (s₁ s₂ : WorldState) (cur : CellId),
        AgreesOnVisible f s₁ s₂ →
        projectViewList f s₁ cur vs = projectViewList f s₂ cur vs
    | .nil, _, _, _, _, _ => rfl
    | .cons hd tl, f, s₁, s₂, cur, h => by
      simp only [projectViewList,
        fog_of_war_viewNode_noninterference hd f s₁ s₂ cur h,
        fog_of_war_viewList_noninterference tl f s₁ s₂ cur h]

  theorem fog_of_war_viewOpt_noninterference :
      ∀ (vo : ViewOpt) (f : Frustum) (s₁ s₂ : WorldState) (cur : CellId),
        AgreesOnVisible f s₁ s₂ →
        projectViewOpt f s₁ cur vo = projectViewOpt f s₂ cur vo
    | .none, _, _, _, _, _ => rfl
    | .some n, f, s₁, s₂, cur, h => by
      simp only [projectViewOpt, fog_of_war_viewNode_noninterference n f s₁ s₂ cur h]
end

def mutateSlot (s : WorldState) (targetCell : CellId) (targetSlot newVal : Nat) : WorldState :=
  fun c k => if c = targetCell ∧ k = targetSlot then newVal else s c k

theorem severed_secret_mutation_invisible (f : Frustum) (s : WorldState)
    (cur secretCell : CellId) (secretSlot newVal : Nat) (v : ViewNode)
    (hhidden : (secretCell, secretSlot) ∉ f.visibleSlots) :
    projectViewNode f (mutateSlot s secretCell secretSlot newVal) cur v =
      projectViewNode f s cur v := by
  apply fog_of_war_viewNode_noninterference
  intro c k hmem; unfold mutateSlot
  have hne : ¬ (c = secretCell ∧ k = secretSlot) := by rintro ⟨rfl, rfl⟩; exact hhidden hmem
  simp [hne]

theorem sever_host_erases_subtree (f : Frustum) (s₁ s₂ : WorldState) (cur cell : CellId)
    (st₁ st₂ : HostStatus) (sub₁ sub₂ : ViewOpt) (digest : Nat)
    (hsev : f.policy cell = .sever digest) :
    projectViewNode f s₁ cur (.host cell st₁ sub₁) =
      projectViewNode f s₂ cur (.host cell st₂ sub₂) := by
  simp [projectViewNode, hsev]

/-! ### A.2 Deterministic Tree-Diff / Patch Roundtrip -/

inductive ContainerTag where
  | vstack | row | list | table | sectionBox | tabs | grid
  deriving DecidableEq, Repr

mutual
  inductive ViewPatch where
    | keep
    | replace (node : ViewNode)
    | patchContainer (tag : ContainerTag) (patches : ViewPatchList)
    | patchHost (subPatch : ViewPatchOpt)
    | patchAdept (innerPatch : ViewPatch)
    deriving DecidableEq, Repr

  inductive ViewPatchList where
    | nil | cons (hd : ViewPatch) (tl : ViewPatchList)
    deriving DecidableEq, Repr

  inductive ViewPatchOpt where
    | none | some (patch : ViewPatch)
    deriving DecidableEq, Repr
end

mutual
  def diff (v v' : ViewNode) : ViewPatch :=
    if v = v' then .keep
    else match v, v' with
      | .vstack cs, .vstack cs' =>
        if cs.length = cs'.length then .patchContainer .vstack (diffList cs cs')
        else .replace (.vstack cs')
      | .row cs, .row cs' =>
        if cs.length = cs'.length then .patchContainer .row (diffList cs cs')
        else .replace (.row cs')
      | .list cs, .list cs' =>
        if cs.length = cs'.length then .patchContainer .list (diffList cs cs')
        else .replace (.list cs')
      | .table rs, .table rs' =>
        if rs.length = rs'.length then .patchContainer .table (diffList rs rs')
        else .replace (.table rs')
      | .sectionBox t₁ g₁ cs, .sectionBox t₂ g₂ cs' =>
        if t₁ = t₂ ∧ g₁ = g₂ ∧ cs.length = cs'.length then
          .patchContainer .sectionBox (diffList cs cs')
        else .replace (.sectionBox t₂ g₂ cs')
      | .tabs l₁ s₁ t₁ r₁ ps, .tabs l₂ s₂ t₂ r₂ ps' =>
        if l₁ = l₂ ∧ s₁ = s₂ ∧ t₁ = t₂ ∧ r₁ = r₂ ∧ ps.length = ps'.length then
          .patchContainer .tabs (diffList ps ps')
        else .replace (.tabs l₂ s₂ t₂ r₂ ps')
      | .grid c₁ cs, .grid c₂ cs' =>
        if c₁ = c₂ ∧ cs.length = cs'.length then .patchContainer .grid (diffList cs cs')
        else .replace (.grid c₂ cs')
      | .host id₁ st₁ (.some n₁), .host id₂ st₂ (.some n₂) =>
        if id₁ = id₂ ∧ st₁ = st₂ then .patchHost (.some (diff n₁ n₂))
        else .replace (.host id₂ st₂ (.some n₂))
      | .adept inner₁, .adept inner₂ => .patchAdept (diff inner₁ inner₂)
      | _, _ => .replace v'

  def diffList : ViewList → ViewList → ViewPatchList
    | .nil, .nil => .nil
    | .cons h₁ t₁, .cons h₂ t₂ => .cons (diff h₁ h₂) (diffList t₁ t₂)
    | _, _ => .nil
end

mutual
  def applyPatch (v : ViewNode) : ViewPatch → Option ViewNode
    | .keep => some v
    | .replace v' => some v'
    | .patchContainer tag ps =>
      match tag, v with
      | .vstack, .vstack cs => (applyPatchList cs ps).map .vstack
      | .row, .row cs => (applyPatchList cs ps).map .row
      | .list, .list cs => (applyPatchList cs ps).map .list
      | .table, .table rs => (applyPatchList rs ps).map .table
      | .sectionBox, .sectionBox t g cs => (applyPatchList cs ps).map (.sectionBox t g)
      | .tabs, .tabs l s t r ps' => (applyPatchList ps' ps).map (.tabs l s t r)
      | .grid, .grid c cs => (applyPatchList cs ps).map (.grid c)
      | _, _ => none
    | .patchHost subP =>
      match v, subP with
      | .host id st (.some n), .some p' => (applyPatch n p').map (fun n' => .host id st (.some n'))
      | .host id st .none, .none => some (.host id st .none)
      | _, _ => none
    | .patchAdept innerP =>
      match v with | .adept inner => (applyPatch inner innerP).map .adept | _ => none

  def applyPatchList : ViewList → ViewPatchList → Option ViewList
    | .nil, .nil => some .nil
    | .cons h t, .cons hp tp =>
      match applyPatch h hp, applyPatchList t tp with
      | some h', some t' => some (.cons h' t')
      | _, _ => none
    | _, _ => none
end

theorem applyPatch_keep (v : ViewNode) : applyPatch v .keep = some v := by simp [applyPatch]
theorem diff_self_keep (v : ViewNode) : diff v v = .keep := by unfold diff; simp

mutual
  /-- **Deterministic Tree-Diff / Patch Roundtrip**: `∀ v v', applyPatch v (diff v v') = some v'`. -/
  theorem applyPatch_diff : ∀ (v v' : ViewNode), applyPatch v (diff v v') = some v'
    | .vstack cs, v' => by
      unfold diff; by_cases heq : ViewNode.vstack cs = v'
      · subst heq; simp [applyPatch]
      · cases v' <;> simp only [heq, ite_false, applyPatch]
        rename_i cs'; by_cases hl : cs.length = cs'.length <;> simp [hl, applyPatch, applyPatchList_diffList]
    | .row cs, v' => by
      unfold diff; by_cases heq : ViewNode.row cs = v'
      · subst heq; simp [applyPatch]
      · cases v' <;> simp only [heq, ite_false, applyPatch]
        rename_i cs'; by_cases hl : cs.length = cs'.length <;> simp [hl, applyPatch, applyPatchList_diffList]
    | .list cs, v' => by
      unfold diff; by_cases heq : ViewNode.list cs = v'
      · subst heq; simp [applyPatch]
      · cases v' <;> simp only [heq, ite_false, applyPatch]
        rename_i cs'; by_cases hl : cs.length = cs'.length <;> simp [hl, applyPatch, applyPatchList_diffList]
    | .table rs, v' => by
      unfold diff; by_cases heq : ViewNode.table rs = v'
      · subst heq; simp [applyPatch]
      · cases v' <;> simp only [heq, ite_false, applyPatch]
        rename_i rs'; by_cases hl : rs.length = rs'.length <;> simp [hl, applyPatch, applyPatchList_diffList]
    | .sectionBox t₁ g₁ cs, v' => by
      unfold diff; by_cases heq : ViewNode.sectionBox t₁ g₁ cs = v'
      · subst heq; simp [applyPatch]
      · cases v' <;> simp only [heq, ite_false, applyPatch]
        rename_i t₂ g₂ cs'; by_cases hm : t₁ = t₂ ∧ g₁ = g₂ ∧ cs.length = cs'.length
        · rcases hm with ⟨rfl, rfl, hl⟩; simp [hl, applyPatch, applyPatchList_diffList cs cs' hl]
        · simp [hm, applyPatch]
    | .tabs l₁ s₁ t₁ r₁ ps, v' => by
      unfold diff; by_cases heq : ViewNode.tabs l₁ s₁ t₁ r₁ ps = v'
      · subst heq; simp [applyPatch]
      · cases v' <;> simp only [heq, ite_false, applyPatch]
        rename_i l₂ s₂ t₂ r₂ ps'
        by_cases hm : l₁ = l₂ ∧ s₁ = s₂ ∧ t₁ = t₂ ∧ r₁ = r₂ ∧ ps.length = ps'.length
        · rcases hm with ⟨rfl, rfl, rfl, rfl, hl⟩; simp [hl, applyPatch, applyPatchList_diffList ps ps' hl]
        · simp [hm, applyPatch]
    | .grid c₁ cs, v' => by
      unfold diff; by_cases heq : ViewNode.grid c₁ cs = v'
      · subst heq; simp [applyPatch]
      · cases v' <;> simp only [heq, ite_false, applyPatch]
        rename_i c₂ cs'; by_cases hm : c₁ = c₂ ∧ cs.length = cs'.length
        · rcases hm with ⟨rfl, hl⟩; simp [hl, applyPatch, applyPatchList_diffList cs cs' hl]
        · simp [hm, applyPatch]
    | .host id₁ st₁ (.some n₁), v' => by
      unfold diff; by_cases heq : ViewNode.host id₁ st₁ (.some n₁) = v'
      · subst heq; simp [applyPatch]
      · cases v' <;> simp only [heq, ite_false, applyPatch]
        rename_i id₂ st₂ sub₂; cases sub₂ with
        | none => simp [applyPatch]
        | some n₂ =>
          by_cases hm : id₁ = id₂ ∧ st₁ = st₂
          · rcases hm with ⟨rfl, rfl⟩; simp [applyPatch, applyPatch_diff n₁ n₂]
          · simp [hm, applyPatch]
    | .adept inner₁, v' => by
      unfold diff; by_cases heq : ViewNode.adept inner₁ = v'
      · subst heq; simp [applyPatch]
      · cases v' <;> simp only [heq, ite_false, applyPatch]
        rename_i inner₂; simp [applyPatch_diff inner₁ inner₂]
    | .text _, v' | .bind _ _ _ _, v' | .button _ _ _, v' | .input _ _ _, v'
    | .gauge _ _ _ _, v' | .divider, v' | .host _ _ .none, v' | .breadcrumb _, v'
    | .progress _ _ _, v' | .pill _ _ _ _ _, v' | .icon _ _, v' | .menu _, v'
    | .halo _ _, v' | .slider _ _ _ _ _, v' | .toggle _ _ _ _ _ _ _, v'
    | .tile _ _ _, v' | .coordGrid _ _, v' => by
      unfold diff; split <;> simp_all [applyPatch]

  theorem applyPatchList_diffList :
      ∀ (vs vs' : ViewList), vs.length = vs'.length →
        applyPatchList vs (diffList vs vs') = some vs'
    | .nil, .nil, _ => by simp [diffList, applyPatchList]
    | .nil, .cons _ _, hlen => by simp [ViewList.length] at hlen; omega
    | .cons _ _, .nil, hlen => by simp [ViewList.length] at hlen
    | .cons h t, .cons h' t', hlen => by
      simp only [ViewList.length, Nat.add_left_cancel_iff] at hlen
      simp only [diffList, applyPatchList, applyPatch_diff h h',
        applyPatchList_diffList t t' hlen]
end

/-! ### A.3 Constructive Repair Badge Synthesis (`Obend.Vault.Affordance:235`) -/

structure RefusalBadge where
  byLaw : String
  reason : String
  missingCaps : List String
  repairHint : Option (String × Nat)
  deriving DecidableEq, Repr

def synthesizeRepairBadge (affName : String) (required held : List String)
    (lawPassed : Bool) (repairHint : Option (String × Nat)) : RefusalBadge :=
  let missing := required.filter (fun r => !held.contains r)
  let capPass := missing.isEmpty
  if !capPass && !lawPassed then
    ⟨affName, "unauthorized and state contract violated", missing, repairHint⟩
  else if !capPass then
    ⟨affName, "unauthorized: missing required capabilities", missing, none⟩
  else if !lawPassed then
    ⟨affName, "state condition unmet: contract violated", [], repairHint⟩
  else ⟨affName, "ok", [], none⟩

theorem synthesizeRepairBadge_ok_iff (affName : String) (required held : List String)
    (lawPassed : Bool) (hint : Option (String × Nat)) :
    (synthesizeRepairBadge affName required held lawPassed hint).reason = "ok" ↔
      (required.filter (fun r => !held.contains r)).isEmpty = true ∧ lawPassed = true := by
  unfold synthesizeRepairBadge
  generalize (required.filter (fun r => !held.contains r)) = ms
  cases ms with
  | nil => cases lawPassed <;> simp
  | cons _ _ => cases lawPassed <;> simp

/-! ## Part B: `S11`-Hardened Electra & CometBFT Light-Client Header Gates -/

def syncCommitteeSize : Nat := 512
def slotsPerSyncCommitteePeriod : Nat := 8192
def finalizedRootDepthAltair : Nat := 6
def finalizedRootDepthElectra : Nat := 7
def execPayloadDepth : Nat := 4
def periodOfSlot (slot : Nat) : Nat := slot / slotsPerSyncCommitteePeriod

structure EthTrustAnchor where
  expectedChainId : Nat
  expectedForkDigest : Nat
  currentPeriod : Nat
  trustedAttestedSlot : Nat
  trustedFinalizedSlot : Nat
  maxStaleness : Nat
  maxClockDrift : Nat
  deriving DecidableEq, Repr

structure EthHeaderUpdate where
  chainId : Nat
  forkDigest : Nat
  attestedSlot : Nat
  signatureSlot : Nat
  finalizedSlot : Nat
  attestedTime : Nat
  committeeLen : Nat
  bitsLen : Nat
  participantCount : Nat
  blsAggOk : Bool
  finalityBranchLen : Nat
  finalityBranchOk : Bool
  execBranchLen : Nat
  execBranchOk : Bool
  deriving DecidableEq, Repr

inductive EthRejectReason where
  | chainIdMismatch | forkDigestMismatch | periodMismatch | futureSlotSpoof
  | finalizedAfterAttested | finalizedHeightRollback | nonMonotonicAttestedSlot
  | staleHeader | futureTimestampSpoof | wrongCommitteeSize | wrongBitfieldLength
  | zeroParticipants | insufficientParticipation | badBlsSignature
  | badFinalityBranch | badExecutionBranch
  deriving DecidableEq, Repr

inductive EthVerdict where | ok | err (reason : EthRejectReason) deriving DecidableEq, Repr

def verifyEthHeaderS11 (anchor : EthTrustAnchor) (u : EthHeaderUpdate) (hostNow : Nat) :
    EthVerdict :=
  if u.chainId ≠ anchor.expectedChainId then .err .chainIdMismatch
  else if u.forkDigest ≠ anchor.expectedForkDigest then .err .forkDigestMismatch
  else if u.signatureSlot < u.attestedSlot then .err .futureSlotSpoof
  else if periodOfSlot u.signatureSlot ≠ anchor.currentPeriod then .err .periodMismatch
  else if u.attestedSlot < u.finalizedSlot then .err .finalizedAfterAttested
  else if u.finalizedSlot < anchor.trustedFinalizedSlot then .err .finalizedHeightRollback
  else if u.attestedSlot ≤ anchor.trustedAttestedSlot then .err .nonMonotonicAttestedSlot
  else if hostNow > u.attestedTime + anchor.maxStaleness then .err .staleHeader
  else if u.attestedTime > hostNow + anchor.maxClockDrift then .err .futureTimestampSpoof
  else if u.committeeLen ≠ syncCommitteeSize then .err .wrongCommitteeSize
  else if u.bitsLen ≠ syncCommitteeSize then .err .wrongBitfieldLength
  else if u.participantCount = 0 then .err .zeroParticipants
  else if u.participantCount * 3 < syncCommitteeSize * 2 then .err .insufficientParticipation
  else if !u.blsAggOk then .err .badBlsSignature
  else if (u.finalityBranchLen ≠ finalizedRootDepthAltair ∧
           u.finalityBranchLen ≠ finalizedRootDepthElectra) ∨ !u.finalityBranchOk then
    .err .badFinalityBranch
  else if u.execBranchLen ≠ execPayloadDepth ∨ !u.execBranchOk then .err .badExecutionBranch
  else .ok

def ethAccepted (anchor : EthTrustAnchor) (u : EthHeaderUpdate) (hostNow : Nat) : Bool :=
  verifyEthHeaderS11 anchor u hostNow == .ok

private theorem ethGuard {p : Prop} [Decidable p] {r : EthRejectReason} {k : EthVerdict}
    (h : (if p then EthVerdict.err r else k) = .ok) : ¬p ∧ k = .ok := by
  by_cases hp : p <;> simp [hp] at h; exact ⟨hp, h⟩

/-- **Electra `S11` Soundness**: acceptance implies every `S11` pin and `≥ 342 / 512` supermajority. -/
theorem ethS11_accepts_implies_pins (anchor : EthTrustAnchor) (u : EthHeaderUpdate)
    (hostNow : Nat) (h : verifyEthHeaderS11 anchor u hostNow = .ok) :
    u.chainId = anchor.expectedChainId ∧ u.forkDigest = anchor.expectedForkDigest ∧
    u.attestedSlot ≤ u.signatureSlot ∧ periodOfSlot u.signatureSlot = anchor.currentPeriod ∧
    anchor.trustedFinalizedSlot ≤ u.finalizedSlot ∧ u.finalizedSlot ≤ u.attestedSlot ∧
    anchor.trustedAttestedSlot < u.attestedSlot ∧
    hostNow ≤ u.attestedTime + anchor.maxStaleness ∧
    u.attestedTime ≤ hostNow + anchor.maxClockDrift ∧
    u.committeeLen = 512 ∧ u.bitsLen = 512 ∧ 342 ≤ u.participantCount ∧
    u.blsAggOk = true ∧ (u.finalityBranchLen = 6 ∨ u.finalityBranchLen = 7) ∧
    u.finalityBranchOk = true ∧ u.execBranchLen = 4 ∧ u.execBranchOk = true := by
  unfold verifyEthHeaderS11 at h
  simp only [syncCommitteeSize, finalizedRootDepthAltair, finalizedRootDepthElectra,
    execPayloadDepth] at h
  obtain ⟨h1, h⟩ := ethGuard h; obtain ⟨h2, h⟩ := ethGuard h
  obtain ⟨h3, h⟩ := ethGuard h; obtain ⟨h4, h⟩ := ethGuard h
  obtain ⟨h5, h⟩ := ethGuard h; obtain ⟨h6, h⟩ := ethGuard h
  obtain ⟨h7, h⟩ := ethGuard h; obtain ⟨h8, h⟩ := ethGuard h
  obtain ⟨h9, h⟩ := ethGuard h; obtain ⟨h10, h⟩ := ethGuard h
  obtain ⟨h11, h⟩ := ethGuard h; obtain ⟨h12, h⟩ := ethGuard h
  obtain ⟨h13, h⟩ := ethGuard h; obtain ⟨h14, h⟩ := ethGuard h
  obtain ⟨h15, h⟩ := ethGuard h; obtain ⟨h16, _⟩ := ethGuard h
  have hbls : u.blsAggOk = true := by cases hb : u.blsAggOk <;> simp_all
  have hfinOk : u.finalityBranchOk = true := by cases hb : u.finalityBranchOk <;> simp_all
  have hexecOk : u.execBranchOk = true := by cases hb : u.execBranchOk <;> simp_all
  have hfinLen : u.finalityBranchLen = 6 ∨ u.finalityBranchLen = 7 := by
    by_cases h6' : u.finalityBranchLen = 6
    · exact Or.inl h6'
    · by_cases h7' : u.finalityBranchLen = 7
      · exact Or.inr h7'
      · exact absurd (Or.inl ⟨h6', h7'⟩) h15
  have hexecLen : u.execBranchLen = 4 := by
    by_cases h4' : u.execBranchLen = 4; · exact h4'
    · exact absurd (Or.inl h4') h16
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, hbls, hfinLen, hfinOk, hexecLen, hexecOk⟩

theorem ethS11_rejects_cross_chain_replay (a : EthTrustAnchor) (u : EthHeaderUpdate) (t : Nat)
    (hne : u.chainId ≠ a.expectedChainId) : verifyEthHeaderS11 a u t = .err .chainIdMismatch := by
  simp [verifyEthHeaderS11, hne]
theorem ethS11_rejects_future_slot_spoof (a : EthTrustAnchor) (u : EthHeaderUpdate) (t : Nat)
    (hlt : u.signatureSlot < u.attestedSlot) : ethAccepted a u t = false := by
  cases h : verifyEthHeaderS11 a u t with
  | err _ => simp [ethAccepted, h] | ok => have hp := ethS11_accepts_implies_pins a u t h; omega
theorem ethS11_rejects_expired_staleness (a : EthTrustAnchor) (u : EthHeaderUpdate) (t : Nat)
    (hs : t > u.attestedTime + a.maxStaleness) : ethAccepted a u t = false := by
  cases h : verifyEthHeaderS11 a u t with
  | err _ => simp [ethAccepted, h] | ok => have hp := ethS11_accepts_implies_pins a u t h; omega
theorem ethS11_rejects_future_time_spoof (a : EthTrustAnchor) (u : EthHeaderUpdate) (t : Nat)
    (hf : u.attestedTime > t + a.maxClockDrift) : ethAccepted a u t = false := by
  cases h : verifyEthHeaderS11 a u t with
  | err _ => simp [ethAccepted, h] | ok => have hp := ethS11_accepts_implies_pins a u t h; omega
theorem ethS11_rejects_sub_supermajority (a : EthTrustAnchor) (u : EthHeaderUpdate) (t : Nat)
    (hlow : u.participantCount ≤ 341) : ethAccepted a u t = false := by
  cases h : verifyEthHeaderS11 a u t with
  | err _ => simp [ethAccepted, h] | ok => have hp := ethS11_accepts_implies_pins a u t h; omega
theorem ethS11_rejects_fork_digest_mismatch (a : EthTrustAnchor) (u : EthHeaderUpdate) (t : Nat)
    (hne : u.forkDigest ≠ a.expectedForkDigest) : ethAccepted a u t = false := by
  cases h : verifyEthHeaderS11 a u t with
  | err _ => simp [ethAccepted, h] | ok => have hp := ethS11_accepts_implies_pins a u t h; exact absurd hp.2.1 hne
theorem ethS11_rejects_finalized_rollback (a : EthTrustAnchor) (u : EthHeaderUpdate) (t : Nat)
    (hback : u.finalizedSlot < a.trustedFinalizedSlot) : ethAccepted a u t = false := by
  cases h : verifyEthHeaderS11 a u t with
  | err _ => simp [ethAccepted, h] | ok => have hp := ethS11_accepts_implies_pins a u t h; omega
theorem ethS11_rejects_period_drift (a : EthTrustAnchor) (u : EthHeaderUpdate) (t : Nat)
    (hper : periodOfSlot u.signatureSlot ≠ a.currentPeriod) : ethAccepted a u t = false := by
  cases h : verifyEthHeaderS11 a u t with
  | err _ => simp [ethAccepted, h] | ok => have hp := ethS11_accepts_implies_pins a u t h; exact absurd hp.2.2.2.1 hper

/-! ### B.2 `S11`-Hardened CometBFT (Cosmos) Adjacent & Skipping Header Gate -/

structure CometTrustAnchor where
  expectedChainId : String
  expectedForkDigest : Nat
  trustedHeight : Nat
  trustedHeaderTime : Nat
  trustingPeriod : Nat
  maxStaleness : Nat
  maxClockDrift : Nat
  deriving DecidableEq, Repr

structure CometHeaderUpdate where
  chainId : String
  forkDigest : Nat
  height : Nat
  headerTime : Nat
  epochBindOk : Bool
  selfBindOk : Bool
  commitMatchesHeader : Bool
  totalPower : Nat
  signedPower : Nat
  trustedTotalPower : Nat
  trustedSignedPower : Nat
  deriving DecidableEq, Repr

inductive CometAdvanceMode where | adjacent | skipping deriving DecidableEq, Repr

inductive CometRejectReason where
  | chainIdMismatch | forkDigestMismatch | nonIncreasingHeight | trustedStateExpired
  | staleHeader | nonMonotonicTime | futureTimestampSpoof | badCommitBinding
  | badSelfBinding | zeroTotalPower | insufficientVotingPower | badEpochBinding
  | zeroTrustedPower | insufficientTrustOverlap
  deriving DecidableEq, Repr

inductive CometVerdict where
  | ok (mode : CometAdvanceMode) | err (reason : CometRejectReason)
  deriving DecidableEq, Repr

def verifyCometHeaderS11 (anchor : CometTrustAnchor) (u : CometHeaderUpdate) (hostNow : Nat) :
    CometVerdict :=
  if u.chainId ≠ anchor.expectedChainId then .err .chainIdMismatch
  else if u.forkDigest ≠ anchor.expectedForkDigest then .err .forkDigestMismatch
  else if u.height ≤ anchor.trustedHeight then .err .nonIncreasingHeight
  else if hostNow ≥ anchor.trustedHeaderTime + anchor.trustingPeriod then .err .trustedStateExpired
  else if hostNow > u.headerTime + anchor.maxStaleness then .err .staleHeader
  else if u.headerTime ≤ anchor.trustedHeaderTime then .err .nonMonotonicTime
  else if u.headerTime > hostNow + anchor.maxClockDrift then .err .futureTimestampSpoof
  else if !u.commitMatchesHeader then .err .badCommitBinding
  else if !u.selfBindOk then .err .badSelfBinding
  else if u.totalPower = 0 then .err .zeroTotalPower
  else if u.signedPower * 3 ≤ u.totalPower * 2 then .err .insufficientVotingPower
  else if u.height = anchor.trustedHeight + 1 then
    if !u.epochBindOk then .err .badEpochBinding else .ok .adjacent
  else
    if u.trustedTotalPower = 0 then .err .zeroTrustedPower
    else if u.trustedSignedPower * 3 ≤ u.trustedTotalPower then .err .insufficientTrustOverlap
    else .ok .skipping

def cometAccepted (anchor : CometTrustAnchor) (u : CometHeaderUpdate) (hostNow : Nat) : Bool :=
  match verifyCometHeaderS11 anchor u hostNow with | .ok _ => true | .err _ => false

private theorem cometGuard {p : Prop} [Decidable p] {r : CometRejectReason} {k : CometVerdict}
    {m : CometAdvanceMode} (h : (if p then CometVerdict.err r else k) = .ok m) :
    ¬p ∧ k = .ok m := by
  by_cases hp : p <;> simp [hp] at h; exact ⟨hp, h⟩

/-- **CometBFT `S11` Soundness**: acceptance implies all `S11` pins, strict `> 2/3` voting power,
and exact disjoint adjacent vs skipping evidence. -/
theorem cometS11_accepts_implies_pins (anchor : CometTrustAnchor) (u : CometHeaderUpdate)
    (hostNow : Nat) (mode : CometAdvanceMode)
    (h : verifyCometHeaderS11 anchor u hostNow = .ok mode) :
    u.chainId = anchor.expectedChainId ∧ u.forkDigest = anchor.expectedForkDigest ∧
    anchor.trustedHeight < u.height ∧
    hostNow < anchor.trustedHeaderTime + anchor.trustingPeriod ∧
    hostNow ≤ u.headerTime + anchor.maxStaleness ∧
    anchor.trustedHeaderTime < u.headerTime ∧
    u.headerTime ≤ hostNow + anchor.maxClockDrift ∧
    u.commitMatchesHeader = true ∧ u.selfBindOk = true ∧
    0 < u.totalPower ∧ u.totalPower * 2 < u.signedPower * 3 ∧
    ((mode = .adjacent ∧ u.height = anchor.trustedHeight + 1 ∧ u.epochBindOk = true) ∨
     (mode = .skipping ∧ anchor.trustedHeight + 1 < u.height ∧
      0 < u.trustedTotalPower ∧ u.trustedTotalPower < u.trustedSignedPower * 3)) := by
  unfold verifyCometHeaderS11 at h
  obtain ⟨h1, h⟩ := cometGuard h; obtain ⟨h2, h⟩ := cometGuard h
  obtain ⟨h3, h⟩ := cometGuard h; obtain ⟨h4, h⟩ := cometGuard h
  obtain ⟨h5, h⟩ := cometGuard h; obtain ⟨h6, h⟩ := cometGuard h
  obtain ⟨h7, h⟩ := cometGuard h; obtain ⟨h8, h⟩ := cometGuard h
  obtain ⟨h9, h⟩ := cometGuard h; obtain ⟨h10, h⟩ := cometGuard h
  obtain ⟨h11, h⟩ := cometGuard h
  have hcid : u.chainId = anchor.expectedChainId := by
    by_cases hc : u.chainId = anchor.expectedChainId; · exact hc
    · exact absurd hc h1
  have hcm : u.commitMatchesHeader = true := by cases hb : u.commitMatchesHeader <;> simp_all
  have hsb : u.selfBindOk = true := by cases hb : u.selfBindOk <;> simp_all
  refine ⟨hcid, by omega, by omega, by omega, by omega, by omega, by omega, hcm, hsb,
    by omega, by omega, ?_⟩
  by_cases hadj : u.height = anchor.trustedHeight + 1
  · simp only [hadj, ite_true] at h
    obtain ⟨hepb, hok⟩ := cometGuard h; cases hok
    have hepb' : u.epochBindOk = true := by cases hb : u.epochBindOk <;> simp_all
    exact Or.inl ⟨rfl, hadj, hepb'⟩
  · simp only [hadj, ite_false] at h
    obtain ⟨htp, h⟩ := cometGuard h; obtain ⟨hov, hok⟩ := cometGuard h; cases hok
    exact Or.inr ⟨rfl, by omega, by omega, by omega⟩

theorem cometS11_rejects_cross_chain_replay (a : CometTrustAnchor) (u : CometHeaderUpdate)
    (t : Nat) (hne : u.chainId ≠ a.expectedChainId) :
    verifyCometHeaderS11 a u t = .err .chainIdMismatch := by simp [verifyCometHeaderS11, hne]
theorem cometS11_rejects_expired_trust_period (a : CometTrustAnchor) (u : CometHeaderUpdate)
    (t : Nat) (hexp : t ≥ a.trustedHeaderTime + a.trustingPeriod) : cometAccepted a u t = false := by
  cases h : verifyCometHeaderS11 a u t with
  | err _ => simp [cometAccepted, h] | ok m => have hp := cometS11_accepts_implies_pins a u t m h; omega
theorem cometS11_rejects_stale_header (a : CometTrustAnchor) (u : CometHeaderUpdate) (t : Nat)
    (hs : t > u.headerTime + a.maxStaleness) : cometAccepted a u t = false := by
  cases h : verifyCometHeaderS11 a u t with
  | err _ => simp [cometAccepted, h] | ok m => have hp := cometS11_accepts_implies_pins a u t m h; omega
theorem cometS11_rejects_future_time_spoof (a : CometTrustAnchor) (u : CometHeaderUpdate)
    (t : Nat) (hf : u.headerTime > t + a.maxClockDrift) : cometAccepted a u t = false := by
  cases h : verifyCometHeaderS11 a u t with
  | err _ => simp [cometAccepted, h] | ok m => have hp := cometS11_accepts_implies_pins a u t m h; omega
theorem cometS11_rejects_insufficient_voting_power (a : CometTrustAnchor)
    (u : CometHeaderUpdate) (t : Nat) (hlow : u.signedPower * 3 ≤ u.totalPower * 2) :
    cometAccepted a u t = false := by
  cases h : verifyCometHeaderS11 a u t with
  | err _ => simp [cometAccepted, h] | ok m => have hp := cometS11_accepts_implies_pins a u t m h; omega
theorem cometS11_rejects_zero_overlap_skip (a : CometTrustAnchor) (u : CometHeaderUpdate)
    (t : Nat) (hskip : a.trustedHeight + 1 < u.height) (hzero : u.trustedSignedPower = 0) :
    cometAccepted a u t = false := by
  cases h : verifyCometHeaderS11 a u t with
  | err _ => simp [cometAccepted, h]
  | ok m =>
    have hp := cometS11_accepts_implies_pins a u t m h
    rcases hp.2.2.2.2.2.2.2.2.2.2.2 with ⟨_, hadj, _⟩ | ⟨_, _, _, hov⟩ <;> omega

/-! ## Part C: Premise Inhabitation Witnesses, Golden Vectors & `#tooth` Falsifiers -/

section WitnessesAndTeeth

private def demoFrustum : Frustum :=
  { viewer := "alice", visibleSlots := [("root", 0)]
    policy := fun c =>
      if c = "vault-secret" then .sever 0xBEEF
      else if c = "mock-oracle" then .interpose "cached-price"
      else if c = "shared-doc" then .attenuate [("shared-doc", 1)]
      else .tether }

private def demoTree : ViewNode :=
  .vstack (.cons (.bind 0 "public_balance" .amount none)
    (.cons (.host "vault-secret" .live (.some (.bind 7 "private_key_share" .hex none)))
      (.cons (.host "mock-oracle" .live (.some (.gauge 2 100 "oracle" none))) .nil)))

private def worldA : WorldState | "root", 0 => 1000 | "vault-secret", 7 => 42 | _, _ => 0
private def worldB : WorldState | "root", 0 => 1000 | "vault-secret", 7 => 999999 | _, _ => 0
private def worldVis : WorldState | "root", 0 => 2500 | "vault-secret", 7 => 42 | _, _ => 0

theorem witness_severed_secret_unchanged :
    projectViewNode demoFrustum worldA "root" demoTree =
      projectViewNode demoFrustum worldB "root" demoTree := by decide

theorem tooth_visible_slot_mutation_changes_projection :
    projectViewNode demoFrustum worldA "root" demoTree ≠
      projectViewNode demoFrustum worldVis "root" demoTree := by decide

theorem tooth_applyPatch_mismatched_container_refused :
    applyPatch (.row (.cons (.text "a") .nil))
      (.patchContainer .vstack (.cons .keep .nil)) = none := by decide

theorem witness_repair_badge_missing_cap :
    synthesizeRepairBadge "publish" ["cap.write", "cap.sign"] ["cap.write"] true none =
      ⟨"publish", "unauthorized: missing required capabilities", ["cap.sign"], none⟩ := rfl

def goldenEthAnchor : EthTrustAnchor :=
  { expectedChainId := 1, expectedForkDigest := 0x6A95A1A9, currentPeriod := 1800
    trustedAttestedSlot := 14745600, trustedFinalizedSlot := 14745536
    maxStaleness := 3600, maxClockDrift := 60 }

def goldenEthElectra397 : EthHeaderUpdate :=
  { chainId := 1, forkDigest := 0x6A95A1A9, attestedSlot := 14745664
    signatureSlot := 14745665, finalizedSlot := 14745600, attestedTime := 1780000000
    committeeLen := 512, bitsLen := 512, participantCount := 397, blsAggOk := true
    finalityBranchLen := 7, finalityBranchOk := true, execBranchLen := 4, execBranchOk := true }

def goldenEthHostNow : Nat := 1780000120

theorem goldenEthElectra397_accepts :
    verifyEthHeaderS11 goldenEthAnchor goldenEthElectra397 goldenEthHostNow = .ok := by decide

theorem goldenEthElectra342_accepts :
    verifyEthHeaderS11 goldenEthAnchor { goldenEthElectra397 with participantCount := 342 }
      goldenEthHostNow = .ok := by decide

theorem tooth_goldenEth_341_rejected :
    verifyEthHeaderS11 goldenEthAnchor { goldenEthElectra397 with participantCount := 341 }
      goldenEthHostNow = .err .insufficientParticipation := by decide

theorem tooth_goldenEth_crossChain_rejected :
    verifyEthHeaderS11 goldenEthAnchor { goldenEthElectra397 with chainId := 11155111 }
      goldenEthHostNow = .err .chainIdMismatch := by decide

theorem tooth_goldenEth_futureSlot_rejected :
    verifyEthHeaderS11 goldenEthAnchor { goldenEthElectra397 with signatureSlot := 14745663 }
      goldenEthHostNow = .err .futureSlotSpoof := by decide

theorem tooth_goldenEth_stale_rejected :
    verifyEthHeaderS11 goldenEthAnchor goldenEthElectra397 (1780000000 + 3601) =
      .err .staleHeader := by decide

def goldenCometAnchor : CometTrustAnchor :=
  { expectedChainId := "cosmoshub-4", expectedForkDigest := 0xC0540504
    trustedHeight := 26000000, trustedHeaderTime := 1780000000
    trustingPeriod := 1209600, maxStaleness := 3600, maxClockDrift := 60 }

def goldenCometAdjacent : CometHeaderUpdate :=
  { chainId := "cosmoshub-4", forkDigest := 0xC0540504, height := 26000001
    headerTime := 1780000006, epochBindOk := true, selfBindOk := true
    commitMatchesHeader := true, totalPower := 300, signedPower := 201
    trustedTotalPower := 300, trustedSignedPower := 201 }

def goldenCometSkip95 : CometHeaderUpdate :=
  { chainId := "cosmoshub-4", forkDigest := 0xC0540504, height := 26000095
    headerTime := 1780000570, epochBindOk := false, selfBindOk := true
    commitMatchesHeader := true, totalPower := 300, signedPower := 240
    trustedTotalPower := 300, trustedSignedPower := 101 }

theorem goldenCometAdjacent_accepts :
    verifyCometHeaderS11 goldenCometAnchor goldenCometAdjacent 1780000020 =
      .ok .adjacent := by decide

theorem goldenCometSkip95_accepts :
    verifyCometHeaderS11 goldenCometAnchor goldenCometSkip95 1780000600 =
      .ok .skipping := by decide

theorem tooth_goldenComet_crossChain_rejected :
    verifyCometHeaderS11 goldenCometAnchor
      { goldenCometAdjacent with chainId := "theta-testnet-001" } 1780000020 =
      .err .chainIdMismatch := by decide

theorem tooth_goldenComet_expiredTrustPeriod_rejected :
    verifyCometHeaderS11 goldenCometAnchor goldenCometAdjacent (1780000000 + 1209600) =
      .err .trustedStateExpired := by decide

theorem tooth_goldenComet_exactTwoThirds_rejected :
    verifyCometHeaderS11 goldenCometAnchor
      { goldenCometAdjacent with signedPower := 200 } 1780000020 =
      .err .insufficientVotingPower := by decide

theorem tooth_goldenComet_zeroOverlapSkip_rejected :
    verifyCometHeaderS11 goldenCometAnchor
      { goldenCometSkip95 with trustedSignedPower := 0 } 1780000600 =
      .err .insufficientTrustOverlap := by decide

end WitnessesAndTeeth

/-! ## Part D: `#guard_msgs`-Pinned Axiom Audit -/

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.fog_of_war_viewNode_noninterference' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fog_of_war_viewNode_noninterference

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.severed_secret_mutation_invisible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms severed_secret_mutation_invisible

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.applyPatch_diff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyPatch_diff

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.ethS11_accepts_implies_pins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ethS11_accepts_implies_pins

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.ethS11_rejects_cross_chain_replay' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms ethS11_rejects_cross_chain_replay

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.ethS11_rejects_future_slot_spoof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ethS11_rejects_future_slot_spoof

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.ethS11_rejects_expired_staleness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ethS11_rejects_expired_staleness

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.cometS11_accepts_implies_pins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cometS11_accepts_implies_pins

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.cometS11_rejects_expired_trust_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cometS11_rejects_expired_trust_period

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.cometS11_rejects_zero_overlap_skip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cometS11_rejects_zero_overlap_skip

end Minidregg.Assurance.LightClientAndViewLens
