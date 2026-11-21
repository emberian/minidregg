/-
# `Assurance/LightClientAndViewLens.lean`

Machine-checked Lean `v4.35.0` assurance module for the Wave-8 `deos-view` and
`eth-lightclient` / `cosmos-lightclient` quarry blueprints (`Phase 1` `obend-surfaces`
and `obend-lightclients`):

- **Part A (`Frustum`-Filtered 25-Variant `ViewNode` IR):**
  1. Complete toolkit-free 25-variant `ViewNode` IR mirrored from `breadstuffs/deos-view/src/tree.rs:25-249`.
  2. Boundary cut `Disposition` (`sever / attenuate / interpose / tether`, from
     `obend/lean/Obend/Vault/FrustumMembrane.lean:661`) and `Frustum` observer projection.
  3. **Fog-of-War Observer Non-Interference** (`fog_of_war_viewNode_noninterference` and
     `severed_secret_mutation_invisible`): arbitrary mutations outside `frustum.visibleSlots`
     (including inside `sever`ed or `interpose`d secret cells) produce identical projected trees.
  4. **Deterministic Tree-Diff / Patch Roundtrip** (`applyPatch_diff`):
     `∀ v v', applyPatch v (diff v v') = some v'`, plus identity and mismatch `#tooth` falsifiers.
  5. **Constructive Repair Badge Synthesis** (`synthesizeRepairBadge`, mirroring
     `obend/lean/Obend/Vault/Affordance.lean:235`).

- **Part B (`S11`-Hardened Electra & CometBFT Light-Client Header Gates):**
  1. Electra sync-committee (`≥ 342/512`, including mainnet `397/512`) header admission with
     mandatory `S11` pins: `expectedChainId`, `attestedSlot ≤ signatureSlot`, slot-derived
     sync-committee period (`slot / 8192`), `hostNow ≤ attestedTime + maxStaleness`,
     `attestedTime ≤ hostNow + maxClockDrift`, domain-separated `forkDigest`, and
     non-decreasing `finalizedSlot`.
  2. CometBFT adjacent (`height = trusted + 1`) and skipping (`height > trusted + 1`,
     `> 1/3` trust overlap) header admission with strict `> 2/3` voting power and mandatory
     `S11` chain/fork/freshness/trusting-period pins.
  3. Universal refusal theorems, `#tooth` falsifiers, and concrete golden-vector witnesses
     shared with the standalone Rust `quarried_shells` conformance suite.
-/

namespace Minidregg.Assurance.LightClientAndViewLens

set_option autoImplicit false

/-! ## Part A: Toolkit-Free 25-Variant `ViewNode` IR & `Frustum` Non-Interference -/

abbrev CellId := String

/-- Display formatting for `ViewNode.bind` (`deos-view/src/fmt.rs:24`). -/
inductive BindFmt where
  | raw
  | hex
  | id
  | amount
  deriving DecidableEq, Repr

/-- Progressive disclosure level (`deos-view/src/tree.rs:267`). -/
inductive Disclosure where
  | simple
  | adept
  deriving DecidableEq, Repr

/-- Value-to-label case for live `ViewNode.pill` (`deos-view/src/tree.rs:254`). -/
structure PillCase where
  value : Nat
  label : String
  tag : String
  deriving DecidableEq, Repr

/-- Breadcrumb segment (`deos-view/src/tree.rs:347`). -/
structure Crumb where
  label : String
  turn : String
  arg : Int
  deriving DecidableEq, Repr

/-- Context menu row (`deos-view/src/tree.rs:356`). -/
structure MenuItem where
  label : String
  turn : String
  arg : Int
  enabled : Bool
  wantsText : Bool
  deriving DecidableEq, Repr

/-- Pharo direct-manipulation handle (`deos-view/src/tree.rs:386`). -/
structure HaloHandle where
  glyph : String
  turn : String
  arg : Int
  enabled : Bool
  deriving DecidableEq, Repr

/-- Coordinate-addressed board square (`deos-view/src/tree.rs:400`). -/
structure CoordCell where
  glyph : String
  tag : String
  turn : String
  arg : Int
  highlight : Bool
  deriving DecidableEq, Repr

/-- Projection status carried by a mounted `ViewNode.host` node after frustum filtering. -/
inductive HostStatus where
  | live
  | severed (snapshotDigest : Nat)
  | attenuated (allowedCount : Nat)
  | interposed (mockLabel : String)
  deriving DecidableEq, Repr

mutual
  /-- Complete 25-variant toolkit-free `ViewNode` IR matching `deos-view/src/tree.rs:25-249`.
  Live slot-reading nodes (`bind`, `tabs`, `gauge`, `pill`, `slider`, `toggle`) carry an
  `Option Nat` resolved slot reading (`none` when unresolved or fog-of-war scrubbed). -/
  inductive ViewNode where
    -- 1..8: core layout & interactive nodes
    | vstack (children : ViewList)
    | row (children : ViewList)
    | text (body : String)
    | bind (slot : Nat) (label : String) (fmt : BindFmt) (resolved : Option Nat)
    | button (label turn : String) (arg : Int)
    | input (bindView fireTurn submitLabel : String)
    | list (items : ViewList)
    | table (rows : ViewList)
    -- 9..12: richness expansion batch 1
    | section (title tag : String) (children : ViewList)
    | tabs (labels : List String) (selectedSlot : Nat) (selectTurn : String)
        (resolvedActive : Option Nat) (panels : ViewList)
    | gauge (slot maxVal : Nat) (label : String) (resolved : Option Nat)
    | divider
    -- 13: fractal cell-hosted composition keystone
    | host (cell : CellId) (status : HostStatus) (view : ViewOpt)
    -- 14..24: richness expansion batch 2
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
    -- 25: progressive disclosure marker
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

/-- Number of child nodes in a `ViewList`. -/
def ViewList.length : ViewList → Nat
  | .nil => 0
  | .cons _ tl => 1 + tl.length

/-- Boundary-cut disposition for a hosted cell crossing a viewer's frustum,
mirroring `Obend.Vault.FrustumMembrane.Disposition` (`FrustumMembrane.lean:661`). -/
inductive Disposition where
  | sever (snapshotDigest : Nat)
  | attenuate (allowedSlots : List (CellId × Nat))
  | interpose (mockLabel : String)
  | tether
  deriving DecidableEq, Repr

/-- An observer's fog-of-war frustum: the exact `(cell, slot)` pairs visible to the viewer
plus the boundary-cut disposition applied when entering any hosted child cell. -/
structure Frustum where
  viewer : CellId
  visibleSlots : List (CellId × Nat)
  policy : CellId → Disposition

/-- Narrow a frustum to the intersection with `allowed`, ensuring attenuation can only shrink
visibility and never grant access outside the outer frustum. -/
def Frustum.restrict (f : Frustum) (allowed : List (CellId × Nat)) : Frustum :=
  { f with visibleSlots := f.visibleSlots.filter (fun p => allowed.contains p) }

/-- Abstract world store mapping `(cell, slot)` to its live scalar value. -/
abbrev WorldState := CellId → Nat → Nat

/-- Two worlds agree on every slot visible inside `frustum`. -/
def AgreesOnVisible (f : Frustum) (s₁ s₂ : WorldState) : Prop :=
  ∀ c k, (c, k) ∈ f.visibleSlots → s₁ c k = s₂ c k

theorem agreesOnVisible_restrict {f : Frustum} {allowed : List (CellId × Nat)}
    {s₁ s₂ : WorldState} (h : AgreesOnVisible f s₁ s₂) :
    AgreesOnVisible (f.restrict allowed) s₁ s₂ := by
  intro c k hmem
  exact h c k (List.mem_filter.mp hmem).1

/-- Frustum-filtered slot read: returns `some (state cell slot)` iff `(cell, slot)` lies in
`frustum.visibleSlots`, otherwise returns `none` (scrubbed) without inspecting `state`. -/
def readVisibleSlot (f : Frustum) (s : WorldState) (cell : CellId) (slot : Nat) : Option Nat :=
  if f.visibleSlots.contains (cell, slot) then some (s cell slot) else none

theorem readVisibleSlot_eq_of_agrees {f : Frustum} {s₁ s₂ : WorldState}
    (h : AgreesOnVisible f s₁ s₂) (cell : CellId) (slot : Nat) :
    readVisibleSlot f s₁ cell slot = readVisibleSlot f s₂ cell slot := by
  unfold readVisibleSlot
  cases hc : f.visibleSlots.contains (cell, slot) with
  | false => rfl
  | true =>
    have hmem : (cell, slot) ∈ f.visibleSlots := List.mem_of_elem_eq_true hc
    simp [h cell slot hmem]

mutual
  /-- Project a `ViewNode` tree through a fog-of-war `Frustum` against `state`.
  - Live slot-reading nodes consult `readVisibleSlot` (scrubbed outside `frustum.visibleSlots`).
  - Hosted child cells are filtered by `frustum.policy cell`:
    * `.sever digest` scrubs the entire hosted subtree and replaces it with a digest pin.
    * `.attenuate allowed` narrows `frustum` to `frustum.restrict allowed` before recursing.
    * `.interpose mock` replaces the hosted subtree with a static mock label.
    * `.tether` recurses live under the current frustum. -/
  def projectViewNode (f : Frustum) (s : WorldState) (cur : CellId) : ViewNode → ViewNode
    | .vstack cs => .vstack (projectViewList f s cur cs)
    | .row cs => .row (projectViewList f s cur cs)
    | .text body => .text body
    | .bind slot lbl fmt _ => .bind slot lbl fmt (readVisibleSlot f s cur slot)
    | .button lbl turn arg => .button lbl turn arg
    | .input bv ft sl => .input bv ft sl
    | .list cs => .list (projectViewList f s cur cs)
    | .table rs => .table (projectViewList f s cur rs)
    | .section title tag cs => .section title tag (projectViewList f s cur cs)
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
      let r := match oslot with
        | some sl => readVisibleSlot f s cur sl
        | none => none
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
  /-- **Fog-of-War Observer Non-Interference**: whenever two worlds `s₁` and `s₂` agree on
  `frustum.visibleSlots`, projecting ANY 25-variant `ViewNode` tree yields identical output,
  even when hidden or `sever`ed secret cells mutate arbitrarily. -/
  theorem fog_of_war_viewNode_noninterference (v : ViewNode) :
      ∀ (f : Frustum) (s₁ s₂ : WorldState) (cur : CellId),
        AgreesOnVisible f s₁ s₂ →
        projectViewNode f s₁ cur v = projectViewNode f s₂ cur v := by
    cases v with
    | vstack cs =>
      intro f s₁ s₂ cur h
      simp only [projectViewNode, fog_of_war_viewList_noninterference cs f s₁ s₂ cur h]
    | row cs =>
      intro f s₁ s₂ cur h
      simp only [projectViewNode, fog_of_war_viewList_noninterference cs f s₁ s₂ cur h]
    | text _ => intro _ _ _ _ _; rfl
    | bind slot lbl fmt _ =>
      intro f s₁ s₂ cur h
      simp only [projectViewNode, readVisibleSlot_eq_of_agrees h cur slot]
    | button _ _ _ => intro _ _ _ _ _; rfl
    | input _ _ _ => intro _ _ _ _ _; rfl
    | list cs =>
      intro f s₁ s₂ cur h
      simp only [projectViewNode, fog_of_war_viewList_noninterference cs f s₁ s₂ cur h]
    | table rs =>
      intro f s₁ s₂ cur h
      simp only [projectViewNode, fog_of_war_viewList_noninterference rs f s₁ s₂ cur h]
    | section title tag cs =>
      intro f s₁ s₂ cur h
      simp only [projectViewNode, fog_of_war_viewList_noninterference cs f s₁ s₂ cur h]
    | tabs lbls sel turn _ ps =>
      intro f s₁ s₂ cur h
      simp only [projectViewNode, readVisibleSlot_eq_of_agrees h cur sel,
        fog_of_war_viewList_noninterference ps f s₁ s₂ cur h]
    | gauge slot maxV lbl _ =>
      intro f s₁ s₂ cur h
      simp only [projectViewNode, readVisibleSlot_eq_of_agrees h cur slot]
    | divider => intro _ _ _ _ _; rfl
    | host cell _ sub =>
      intro f s₁ s₂ cur h
      simp only [projectViewNode]
      cases hp : f.policy cell with
      | sever _ => rfl
      | interpose _ => rfl
      | attenuate allowed =>
        simp only [fog_of_war_viewOpt_noninterference sub (f.restrict allowed) s₁ s₂ cell
          (agreesOnVisible_restrict h)]
      | tether =>
        simp only [fog_of_war_viewOpt_noninterference sub f s₁ s₂ cell h]
    | grid cols cs =>
      intro f s₁ s₂ cur h
      simp only [projectViewNode, fog_of_war_viewList_noninterference cs f s₁ s₂ cur h]
    | breadcrumb _ => intro _ _ _ _ _; rfl
    | progress _ _ _ => intro _ _ _ _ _; rfl
    | pill lbl tag oslot cases _ =>
      intro f s₁ s₂ cur h
      simp only [projectViewNode]
      cases oslot with
      | none => rfl
      | some sl => simp only [readVisibleSlot_eq_of_agrees h cur sl]
    | icon _ _ => intro _ _ _ _ _; rfl
    | menu _ => intro _ _ _ _ _; rfl
    | halo _ _ => intro _ _ _ _ _; rfl
    | slider sl mn mx turn _ =>
      intro f s₁ s₂ cur h
      simp only [projectViewNode, readVisibleSlot_eq_of_agrees h cur sl]
    | toggle sl onT offT gOn gOff lbl _ =>
      intro f s₁ s₂ cur h
      simp only [projectViewNode, readVisibleSlot_eq_of_agrees h cur sl]
    | tile _ _ _ => intro _ _ _ _ _; rfl
    | coordGrid _ _ => intro _ _ _ _ _; rfl
    | adept inner =>
      intro f s₁ s₂ cur h
      simp only [projectViewNode, fog_of_war_viewNode_noninterference inner f s₁ s₂ cur h]

  theorem fog_of_war_viewList_noninterference (vs : ViewList) :
      ∀ (f : Frustum) (s₁ s₂ : WorldState) (cur : CellId),
        AgreesOnVisible f s₁ s₂ →
        projectViewList f s₁ cur vs = projectViewList f s₂ cur vs := by
    cases vs with
    | nil => intro _ _ _ _ _; rfl
    | cons hd tl =>
      intro f s₁ s₂ cur h
      simp only [projectViewList,
        fog_of_war_viewNode_noninterference hd f s₁ s₂ cur h,
        fog_of_war_viewList_noninterference tl f s₁ s₂ cur h]

  theorem fog_of_war_viewOpt_noninterference (vo : ViewOpt) :
      ∀ (f : Frustum) (s₁ s₂ : WorldState) (cur : CellId),
        AgreesOnVisible f s₁ s₂ →
        projectViewOpt f s₁ cur vo = projectViewOpt f s₂ cur vo := by
    cases vo with
    | none => intro _ _ _ _ _; rfl
    | some n =>
      intro f s₁ s₂ cur h
      simp only [projectViewOpt, fog_of_war_viewNode_noninterference n f s₁ s₂ cur h]
end

/-- Mutate a single slot `(targetCell, targetSlot)` in `s` to `newVal`. -/
def mutateSlot (s : WorldState) (targetCell : CellId) (targetSlot newVal : Nat) : WorldState :=
  fun c k => if c = targetCell ∧ k = targetSlot then newVal else s c k

/-- **Severed / Hidden Secret Mutation Invisibility**: mutating any slot of a `secretCell`
not in `frustum.visibleSlots` is completely invisible to `projectViewNode`. -/
theorem severed_secret_mutation_invisible (f : Frustum) (s : WorldState)
    (cur secretCell : CellId) (secretSlot newVal : Nat) (v : ViewNode)
    (hhidden : (secretCell, secretSlot) ∉ f.visibleSlots) :
    projectViewNode f (mutateSlot s secretCell secretSlot newVal) cur v =
      projectViewNode f s cur v := by
  apply fog_of_war_viewNode_noninterference
  intro c k hmem
  unfold mutateSlot
  have hne : ¬ (c = secretCell ∧ k = secretSlot) := by
    rintro ⟨rfl, rfl⟩
    exact hhidden hmem
  simp [hne]

/-- Severing a hosted cell completely erases its inner subtree and pins only the digest,
regardless of what live widgets or secret binds existed inside. -/
theorem sever_host_erases_subtree (f : Frustum) (s₁ s₂ : WorldState) (cur cell : CellId)
    (st₁ st₂ : HostStatus) (sub₁ sub₂ : ViewOpt) (digest : Nat)
    (hsev : f.policy cell = .sever digest) :
    projectViewNode f s₁ cur (.host cell st₁ sub₁) =
      projectViewNode f s₂ cur (.host cell st₂ sub₂) := by
  simp [projectViewNode, hsev]

/-! ### A.2 Deterministic Tree-Diff / Patch Roundtrip -/

/-- Identifies which container variant a structural child-list patch targets. -/
inductive ContainerTag where
  | vstack | row | list | table | section | tabs | grid
  deriving DecidableEq, Repr

mutual
  /-- Structural diff/patch for `ViewNode` trees. `.keep` preserves unchanged subtrees,
  `.patchContainer` / `.patchHost` / `.patchAdept` update only differing children, and
  `.replace` handles leaf mutations or structural shape changes. -/
  inductive ViewPatch where
    | keep
    | replace (node : ViewNode)
    | patchContainer (tag : ContainerTag) (patches : ViewPatchList)
    | patchHost (subPatch : ViewPatchOpt)
    | patchAdept (innerPatch : ViewPatch)
    deriving DecidableEq, Repr

  inductive ViewPatchList where
    | nil
    | cons (hd : ViewPatch) (tl : ViewPatchList)
    deriving DecidableEq, Repr

  inductive ViewPatchOpt where
    | none
    | some (patch : ViewPatch)
    deriving DecidableEq, Repr
end

mutual
  /-- Deterministic structural diff between two `ViewNode` trees. -/
  def diff : ViewNode → ViewNode → ViewPatch
    | .vstack cs, .vstack cs' =>
      if cs = cs' then .keep
      else if cs.length = cs'.length then .patchContainer .vstack (diffList cs cs')
      else .replace (.vstack cs')
    | .row cs, .row cs' =>
      if cs = cs' then .keep
      else if cs.length = cs'.length then .patchContainer .row (diffList cs cs')
      else .replace (.row cs')
    | .list cs, .list cs' =>
      if cs = cs' then .keep
      else if cs.length = cs'.length then .patchContainer .list (diffList cs cs')
      else .replace (.list cs')
    | .table rs, .table rs' =>
      if rs = rs' then .keep
      else if rs.length = rs'.length then .patchContainer .table (diffList rs rs')
      else .replace (.table rs')
    | .section t₁ g₁ cs, .section t₂ g₂ cs' =>
      if t₁ = t₂ ∧ g₁ = g₂ ∧ cs = cs' then .keep
      else if t₁ = t₂ ∧ g₁ = g₂ ∧ cs.length = cs'.length then
        .patchContainer .section (diffList cs cs')
      else .replace (.section t₂ g₂ cs')
    | .tabs l₁ s₁ t₁ r₁ ps, .tabs l₂ s₂ t₂ r₂ ps' =>
      if l₁ = l₂ ∧ s₁ = s₂ ∧ t₁ = t₂ ∧ r₁ = r₂ ∧ ps = ps' then .keep
      else if l₁ = l₂ ∧ s₁ = s₂ ∧ t₁ = t₂ ∧ r₁ = r₂ ∧ ps.length = ps'.length then
        .patchContainer .tabs (diffList ps ps')
      else .replace (.tabs l₂ s₂ t₂ r₂ ps')
    | .grid c₁ cs, .grid c₂ cs' =>
      if c₁ = c₂ ∧ cs = cs' then .keep
      else if c₁ = c₂ ∧ cs.length = cs'.length then .patchContainer .grid (diffList cs cs')
      else .replace (.grid c₂ cs')
    | .host id₁ st₁ sub₁, .host id₂ st₂ sub₂ =>
      if id₁ = id₂ ∧ st₁ = st₂ ∧ sub₁ = sub₂ then .keep
      else match sub₁, sub₂ with
        | .some n₁, .some n₂ =>
          if id₁ = id₂ ∧ st₁ = st₂ then .patchHost (.some (diff n₁ n₂))
          else .replace (.host id₂ st₂ (.some n₂))
        | _, _ => .replace (.host id₂ st₂ sub₂)
    | .adept inner₁, .adept inner₂ =>
      if inner₁ = inner₂ then .keep else .patchAdept (diff inner₁ inner₂)
    | v, v' =>
      if v = v' then .keep else .replace v'

  def diffList : ViewList → ViewList → ViewPatchList
    | .nil, .nil => .nil
    | .cons h₁ t₁, .cons h₂ t₂ => .cons (diff h₁ h₂) (diffList t₁ t₂)
    | _, _ => .nil
end

mutual
  /-- Apply a `ViewPatch` to a `ViewNode`, failing closed (`none`) on container-tag or arity
  mismatches. -/
  def applyPatch (v : ViewNode) (p : ViewPatch) : Option ViewNode :=
    match p with
    | .keep => some v
    | .replace v' => some v'
    | .patchContainer tag ps =>
      match tag, v with
      | .vstack, .vstack cs => (applyPatchList cs ps).map .vstack
      | .row, .row cs => (applyPatchList cs ps).map .row
      | .list, .list cs => (applyPatchList cs ps).map .list
      | .table, .table rs => (applyPatchList rs ps).map .table
      | .section, .section t g cs => (applyPatchList cs ps).map (.section t g)
      | .tabs, .tabs l s t r ps' => (applyPatchList ps' ps).map (.tabs l s t r)
      | .grid, .grid c cs => (applyPatchList cs ps).map (.grid c)
      | _, _ => none
    | .patchHost subP =>
      match v, subP with
      | .host id st (.some n), .some p' => (applyPatch n p').map (fun n' => .host id st (.some n'))
      | .host id st .none, .none => some (.host id st .none)
      | _, _ => none
    | .patchAdept innerP =>
      match v with
      | .adept inner => (applyPatch inner innerP).map .adept
      | _ => none

  def applyPatchList (vs : ViewList) (ps : ViewPatchList) : Option ViewList :=
    match vs, ps with
    | .nil, .nil => some .nil
    | .cons h t, .cons hp tp =>
      match applyPatch h hp, applyPatchList t tp with
      | some h', some t' => some (.cons h' t')
      | _, _ => none
    | _, _ => none
end

theorem applyPatch_keep (v : ViewNode) : applyPatch v .keep = some v := rfl

theorem diff_self_keep (v : ViewNode) : diff v v = .keep := by
  cases v <;> simp [diff]

mutual
  /-- **Deterministic Tree-Diff / Patch Roundtrip**: for every pair of 25-variant `ViewNode`
  trees `v` and `v'`, applying `diff v v'` to `v` deterministically yields `some v'`. -/
  theorem applyPatch_diff (v v' : ViewNode) : applyPatch v (diff v v') = some v' := by
    cases v <;> cases v' <;> simp only [diff]
    all_goals
      first
      | (split <;> simp_all [applyPatch])
      | (split
         · simp_all [applyPatch]
         · split
           · simp_all [applyPatch, applyPatchList_diffList]
           · simp [applyPatch])
      | (rename_i id₁ st₁ sub₁ id₂ st₂ sub₂
         split
         · simp_all [applyPatch]
         · cases sub₁ <;> cases sub₂
           · simp [applyPatch]
           · simp [applyPatch]
           · simp [applyPatch]
           · rename_i n₁ n₂
             split
             · rename_i heq
               rcases heq with ⟨rfl, rfl⟩
               simp [applyPatch, applyPatch_diff n₁ n₂]
             · simp [applyPatch])

  theorem applyPatchList_diffList (vs vs' : ViewList) (hlen : vs.length = vs'.length) :
      applyPatchList vs (diffList vs vs') = some vs' := by
    cases vs with
    | nil =>
      cases vs' with
      | nil => rfl
      | cons _ _ => simp [ViewList.length] at hlen
    | cons h t =>
      cases vs' with
      | nil => simp [ViewList.length] at hlen
      | cons h' t' =>
        simp only [ViewList.length, Nat.add_left_cancel_iff] at hlen
        simp only [diffList, applyPatchList, applyPatch_diff h h',
          applyPatchList_diffList t t' hlen]
end

/-! ### A.3 Constructive Repair Badge Synthesis (`Obend.Vault.Affordance.synthesizeRepairBadge`) -/

structure RefusalBadge where
  byLaw : String
  reason : String
  missingCaps : List String
  repairHint : Option (String × Nat)
  deriving DecidableEq, Repr

/-- Synthesize an actionable repair badge when an affordance is dark (missing capability
and/or unmet state law). Mirrors `Obend/Vault/Affordance.lean:235`. -/
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
  else
    ⟨affName, "ok", [], none⟩

theorem synthesizeRepairBadge_ok_iff (affName : String) (required held : List String)
    (lawPassed : Bool) (hint : Option (String × Nat)) :
    (synthesizeRepairBadge affName required held lawPassed hint).reason = "ok" ↔
      (required.filter (fun r => !held.contains r)).isEmpty = true ∧ lawPassed = true := by
  unfold synthesizeRepairBadge
  cases hcap : (required.filter (fun r => !held.contains r)).isEmpty <;> cases lawPassed <;> simp

/-! ## Part B: `S11`-Hardened Electra & CometBFT Light-Client Header Gates -/

/-- Altair/Electra sync-committee size (`eth-lightclient/src/lib.rs:63`). -/
def syncCommitteeSize : Nat := 512

/-- Beacon slots per sync-committee period (`EPOCHS_PER_SYNC_COMMITTEE_PERIOD * SLOTS_PER_EPOCH`). -/
def slotsPerSyncCommitteePeriod : Nat := 8192

/-- Altair..Deneb finalized-root branch depth (`gindex 105`, `eth-lightclient/src/finality.rs:42`). -/
def finalizedRootDepthAltair : Nat := 6

/-- Electra+ finalized-root branch depth (`gindex 169`, `eth-lightclient/src/finality.rs:46`). -/
def finalizedRootDepthElectra : Nat := 7

/-- Capella..Electra execution-payload branch depth (`gindex 25`, `eth-lightclient/src/execution.rs:29`). -/
def execPayloadDepth : Nat := 4

/-- Derive the Ethereum sync-committee period directly from the slot (closing `S11`'s
bookkeeping-only `current_period += 1` drift in `eth-lightclient/src/store.rs:304`). -/
def periodOfSlot (slot : Nat) : Nat := slot / slotsPerSyncCommitteePeriod

/-- Pinned trust anchor and `S11` freshness policy for the Ethereum light-client gate. -/
structure EthTrustAnchor where
  expectedChainId : Nat
  expectedForkDigest : Nat
  currentPeriod : Nat
  trustedAttestedSlot : Nat
  trustedFinalizedSlot : Nat
  maxStaleness : Nat
  maxClockDrift : Nat
  deriving DecidableEq, Repr

/-- Incoming Ethereum Electra/Altair `LightClientUpdate` projection carrying all mandatory `S11`
pins (`chainId`, `signatureSlot`, `attestedTime`, `forkDigest`, `finalizedSlot`). -/
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

/-- Exact fail-closed refusal classification for the `S11`-hardened Ethereum gate. -/
inductive EthRejectReason where
  | chainIdMismatch
  | forkDigestMismatch
  | periodMismatch
  | futureSlotSpoof
  | finalizedAfterAttested
  | finalizedHeightRollback
  | nonMonotonicAttestedSlot
  | staleHeader
  | futureTimestampSpoof
  | wrongCommitteeSize
  | wrongBitfieldLength
  | zeroParticipants
  | insufficientParticipation
  | badBlsSignature
  | badFinalityBranch
  | badExecutionBranch
  deriving DecidableEq, Repr

/-- `S11`-hardened Ethereum Electra light-client header admission gate.
Enforces every consensus rule (`512` committee/bitfield, Nomad floor `> 0`, `≥ 2/3`
multiply-form supermajority `3 * p ≥ 2 * 512`, BLS aggregate carrier, Altair/Electra
finality branch depth `6 ∨ 7`, execution branch depth `4`) AND every `S11` pin
(`expectedChainId`, `forkDigest`, slot-derived period, `attestedSlot ≤ signatureSlot`,
`hostNow ≤ attestedTime + maxStaleness`, `attestedTime ≤ hostNow + maxClockDrift`,
non-decreasing `finalizedSlot`). -/
def verifyEthHeaderS11 (anchor : EthTrustAnchor) (u : EthHeaderUpdate) (hostNow : Nat) :
    Except EthRejectReason Unit :=
  if u.chainId ≠ anchor.expectedChainId then .error .chainIdMismatch
  else if u.forkDigest ≠ anchor.expectedForkDigest then .error .forkDigestMismatch
  else if u.signatureSlot < u.attestedSlot then .error .futureSlotSpoof
  else if periodOfSlot u.signatureSlot ≠ anchor.currentPeriod then .error .periodMismatch
  else if u.attestedSlot < u.finalizedSlot then .error .finalizedAfterAttested
  else if u.finalizedSlot < anchor.trustedFinalizedSlot then .error .finalizedHeightRollback
  else if u.attestedSlot ≤ anchor.trustedAttestedSlot then .error .nonMonotonicAttestedSlot
  else if hostNow > u.attestedTime + anchor.maxStaleness then .error .staleHeader
  else if u.attestedTime > hostNow + anchor.maxClockDrift then .error .futureTimestampSpoof
  else if u.committeeLen ≠ syncCommitteeSize then .error .wrongCommitteeSize
  else if u.bitsLen ≠ syncCommitteeSize then .error .wrongBitfieldLength
  else if u.participantCount = 0 then .error .zeroParticipants
  else if u.participantCount * 3 < syncCommitteeSize * 2 then .error .insufficientParticipation
  else if !u.blsAggOk then .error .badBlsSignature
  else if !((u.finalityBranchLen = finalizedRootDepthAltair ∨
             u.finalityBranchLen = finalizedRootDepthElectra) ∧ u.finalityBranchOk) then
    .error .badFinalityBranch
  else if !(u.execBranchLen = execPayloadDepth ∧ u.execBranchOk) then
    .error .badExecutionBranch
  else .ok ()

def ethAccepted (anchor : EthTrustAnchor) (u : EthHeaderUpdate) (hostNow : Nat) : Bool :=
  match verifyEthHeaderS11 anchor u hostNow with
  | .ok () => true
  | .error _ => false

/-- **Electra `S11` Soundness**: acceptance implies all `S11` chain/slot/period/freshness/fork
pins and `≥ 342 / 512` supermajority participation. -/
theorem ethS11_accepts_implies_pins (anchor : EthTrustAnchor) (u : EthHeaderUpdate)
    (hostNow : Nat) (h : verifyEthHeaderS11 anchor u hostNow = .ok ()) :
    u.chainId = anchor.expectedChainId ∧
    u.forkDigest = anchor.expectedForkDigest ∧
    u.attestedSlot ≤ u.signatureSlot ∧
    periodOfSlot u.signatureSlot = anchor.currentPeriod ∧
    anchor.trustedFinalizedSlot ≤ u.finalizedSlot ∧
    u.finalizedSlot ≤ u.attestedSlot ∧
    anchor.trustedAttestedSlot < u.attestedSlot ∧
    hostNow ≤ u.attestedTime + anchor.maxStaleness ∧
    u.attestedTime ≤ hostNow + anchor.maxClockDrift ∧
    u.committeeLen = 512 ∧
    u.bitsLen = 512 ∧
    342 ≤ u.participantCount ∧
    u.blsAggOk = true ∧
    (u.finalityBranchLen = 6 ∨ u.finalityBranchLen = 7) ∧
    u.finalityBranchOk = true ∧
    u.execBranchLen = 4 ∧
    u.execBranchOk = true := by
  unfold verifyEthHeaderS11 at h
  simp only [syncCommitteeSize, finalizedRootDepthAltair, finalizedRootDepthElectra,
    execPayloadDepth] at h
  repeat (split at h; · cases h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega <|>
    simp_all

/-- **`S11` Falsifier 1 — Cross-chain replay is universally rejected.** -/
theorem ethS11_rejects_cross_chain_replay (anchor : EthTrustAnchor) (u : EthHeaderUpdate)
    (hostNow : Nat) (hne : u.chainId ≠ anchor.expectedChainId) :
    verifyEthHeaderS11 anchor u hostNow = .error .chainIdMismatch := by
  simp [verifyEthHeaderS11, hne]

/-- **`S11` Falsifier 2 — Future/inverted slot spoof (`signatureSlot < attestedSlot`) is rejected.** -/
theorem ethS11_rejects_future_slot_spoof (anchor : EthTrustAnchor) (u : EthHeaderUpdate)
    (hostNow : Nat) (hlt : u.signatureSlot < u.attestedSlot) :
    ethAccepted anchor u hostNow = false := by
  unfold ethAccepted verifyEthHeaderS11
  by_cases h1 : u.chainId ≠ anchor.expectedChainId
  · simp [h1]
  · by_cases h2 : u.forkDigest ≠ anchor.expectedForkDigest
    · simp [h1, h2]
    · simp [h1, h2, hlt]

/-- **`S11` Falsifier 3 — Expired / stale header (`hostNow > attestedTime + maxStaleness`) is rejected.** -/
theorem ethS11_rejects_expired_staleness (anchor : EthTrustAnchor) (u : EthHeaderUpdate)
    (hostNow : Nat) (hstale : hostNow > u.attestedTime + anchor.maxStaleness) :
    ethAccepted anchor u hostNow = false := by
  cases h : verifyEthHeaderS11 anchor u hostNow with
  | error _ => simp [ethAccepted, h]
  | ok _ =>
    have hp := ethS11_accepts_implies_pins anchor u hostNow h
    omega

/-- **`S11` Falsifier 4 — Future-timestamp spoof (`attestedTime > hostNow + maxClockDrift`) is rejected.** -/
theorem ethS11_rejects_future_time_spoof (anchor : EthTrustAnchor) (u : EthHeaderUpdate)
    (hostNow : Nat) (hf : u.attestedTime > hostNow + anchor.maxClockDrift) :
    ethAccepted anchor u hostNow = false := by
  cases h : verifyEthHeaderS11 anchor u hostNow with
  | error _ => simp [ethAccepted, h]
  | ok _ =>
    have hp := ethS11_accepts_implies_pins anchor u hostNow h
    omega

/-- **`S11` Falsifier 5 — Sub-supermajority participation (`≤ 341 / 512`) is rejected.** -/
theorem ethS11_rejects_sub_supermajority (anchor : EthTrustAnchor) (u : EthHeaderUpdate)
    (hostNow : Nat) (hlow : u.participantCount ≤ 341) :
    ethAccepted anchor u hostNow = false := by
  cases h : verifyEthHeaderS11 anchor u hostNow with
  | error _ => simp [ethAccepted, h]
  | ok _ =>
    have hp := ethS11_accepts_implies_pins anchor u hostNow h
    omega

/-- **`S11` Falsifier 6 — Wrong domain-separated `forkDigest` is rejected.** -/
theorem ethS11_rejects_fork_digest_mismatch (anchor : EthTrustAnchor) (u : EthHeaderUpdate)
    (hostNow : Nat) (hne : u.forkDigest ≠ anchor.expectedForkDigest) :
    ethAccepted anchor u hostNow = false := by
  cases h : verifyEthHeaderS11 anchor u hostNow with
  | error _ => simp [ethAccepted, h]
  | ok _ =>
    have hp := ethS11_accepts_implies_pins anchor u hostNow h
    exact absurd hp.2.1 hne

/-- **`S11` Falsifier 7 — Finalized height rollback is rejected.** -/
theorem ethS11_rejects_finalized_rollback (anchor : EthTrustAnchor) (u : EthHeaderUpdate)
    (hostNow : Nat) (hback : u.finalizedSlot < anchor.trustedFinalizedSlot) :
    ethAccepted anchor u hostNow = false := by
  cases h : verifyEthHeaderS11 anchor u hostNow with
  | error _ => simp [ethAccepted, h]
  | ok _ =>
    have hp := ethS11_accepts_implies_pins anchor u hostNow h
    omega

/-- **`S11` Falsifier 8 — Period-bookkeeping drift (`periodOfSlot signatureSlot ≠ currentPeriod`) is rejected.** -/
theorem ethS11_rejects_period_drift (anchor : EthTrustAnchor) (u : EthHeaderUpdate)
    (hostNow : Nat) (hper : periodOfSlot u.signatureSlot ≠ anchor.currentPeriod) :
    ethAccepted anchor u hostNow = false := by
  cases h : verifyEthHeaderS11 anchor u hostNow with
  | error _ => simp [ethAccepted, h]
  | ok _ =>
    have hp := ethS11_accepts_implies_pins anchor u hostNow h
    exact absurd hp.2.2.2.1 hper

/-! ### B.2 `S11`-Hardened CometBFT (Cosmos) Adjacent & Skipping Header Gate -/

/-- Pinned trust anchor for the CometBFT light-client gate (`cosmos-lightclient`). -/
structure CometTrustAnchor where
  expectedChainId : String
  expectedForkDigest : Nat
  trustedHeight : Nat
  trustedHeaderTime : Nat
  trustingPeriod : Nat
  maxStaleness : Nat
  maxClockDrift : Nat
  deriving DecidableEq, Repr

/-- Incoming CometBFT signed-header projection covering both adjacent (`h = trusted + 1`)
and skipping (`h > trusted + 1`) verification modes. -/
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

inductive CometAdvanceMode where
  | adjacent
  | skipping
  deriving DecidableEq, Repr

inductive CometRejectReason where
  | chainIdMismatch
  | forkDigestMismatch
  | nonIncreasingHeight
  | trustedStateExpired
  | staleHeader
  | nonMonotonicTime
  | futureTimestampSpoof
  | badCommitBinding
  | badSelfBinding
  | zeroTotalPower
  | insufficientVotingPower
  | badEpochBinding
  | zeroTrustedPower
  | insufficientTrustOverlap
  deriving DecidableEq, Repr

/-- `S11`-hardened CometBFT header admission gate.
Routes `height = trustedHeight + 1` onto adjacent epoch-bound verification and
`height > trustedHeight + 1` onto skipping `> 1/3` trust-overlap verification,
both requiring strict `> 2/3` voting power (`3 * signed > 2 * total`) and all `S11`
chain, fork-digest, trusting-period, staleness, and clock-drift pins. -/
def verifyCometHeaderS11 (anchor : CometTrustAnchor) (u : CometHeaderUpdate) (hostNow : Nat) :
    Except CometRejectReason CometAdvanceMode :=
  if u.chainId ≠ anchor.expectedChainId then .error .chainIdMismatch
  else if u.forkDigest ≠ anchor.expectedForkDigest then .error .forkDigestMismatch
  else if u.height ≤ anchor.trustedHeight then .error .nonIncreasingHeight
  else if hostNow ≥ anchor.trustedHeaderTime + anchor.trustingPeriod then .error .trustedStateExpired
  else if hostNow > u.headerTime + anchor.maxStaleness then .error .staleHeader
  else if u.headerTime ≤ anchor.trustedHeaderTime then .error .nonMonotonicTime
  else if u.headerTime > hostNow + anchor.maxClockDrift then .error .futureTimestampSpoof
  else if !u.commitMatchesHeader then .error .badCommitBinding
  else if !u.selfBindOk then .error .badSelfBinding
  else if u.totalPower = 0 then .error .zeroTotalPower
  else if u.signedPower * 3 ≤ u.totalPower * 2 then .error .insufficientVotingPower
  else if u.height = anchor.trustedHeight + 1 then
    if !u.epochBindOk then .error .badEpochBinding
    else .ok .adjacent
  else
    if u.trustedTotalPower = 0 then .error .zeroTrustedPower
    else if u.trustedSignedPower * 3 ≤ u.trustedTotalPower then .error .insufficientTrustOverlap
    else .ok .skipping

def cometAccepted (anchor : CometTrustAnchor) (u : CometHeaderUpdate) (hostNow : Nat) : Bool :=
  match verifyCometHeaderS11 anchor u hostNow with
  | .ok _ => true
  | .error _ => false

/-- **CometBFT `S11` Soundness**: acceptance implies all `S11` pins, strict `> 2/3` voting power,
and exact disjoint mode evidence (adjacent epoch-bind vs skipping `> 1/3` trust overlap). -/
theorem cometS11_accepts_implies_pins (anchor : CometTrustAnchor) (u : CometHeaderUpdate)
    (hostNow : Nat) (mode : CometAdvanceMode)
    (h : verifyCometHeaderS11 anchor u hostNow = .ok mode) :
    u.chainId = anchor.expectedChainId ∧
    u.forkDigest = anchor.expectedForkDigest ∧
    anchor.trustedHeight < u.height ∧
    hostNow < anchor.trustedHeaderTime + anchor.trustingPeriod ∧
    hostNow ≤ u.headerTime + anchor.maxStaleness ∧
    anchor.trustedHeaderTime < u.headerTime ∧
    u.headerTime ≤ hostNow + anchor.maxClockDrift ∧
    u.commitMatchesHeader = true ∧
    u.selfBindOk = true ∧
    0 < u.totalPower ∧
    u.totalPower * 2 < u.signedPower * 3 ∧
    ((mode = .adjacent ∧ u.height = anchor.trustedHeight + 1 ∧ u.epochBindOk = true) ∨
     (mode = .skipping ∧ anchor.trustedHeight + 1 < u.height ∧
      0 < u.trustedTotalPower ∧ u.trustedTotalPower < u.trustedSignedPower * 3)) := by
  unfold verifyCometHeaderS11 at h
  repeat (split at h; · cases h)
  · -- adjacent branch (u.height = anchor.trustedHeight + 1)
    cases h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Or.inl ⟨rfl, ?_, ?_⟩⟩ <;>
      first | omega | simp_all
  · -- skipping branch (u.height > anchor.trustedHeight + 1)
    cases h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Or.inr ⟨rfl, ?_, ?_, ?_⟩⟩ <;>
      first | omega | simp_all

/-- **`S11` CometBFT Falsifier 1 — Cross-chain replay is rejected.** -/
theorem cometS11_rejects_cross_chain_replay (anchor : CometTrustAnchor) (u : CometHeaderUpdate)
    (hostNow : Nat) (hne : u.chainId ≠ anchor.expectedChainId) :
    verifyCometHeaderS11 anchor u hostNow = .error .chainIdMismatch := by
  simp [verifyCometHeaderS11, hne]

/-- **`S11` CometBFT Falsifier 2 — Expired trusting period is rejected.** -/
theorem cometS11_rejects_expired_trust_period (anchor : CometTrustAnchor) (u : CometHeaderUpdate)
    (hostNow : Nat) (hexp : hostNow ≥ anchor.trustedHeaderTime + anchor.trustingPeriod) :
    cometAccepted anchor u hostNow = false := by
  cases h : verifyCometHeaderS11 anchor u hostNow with
  | error _ => simp [cometAccepted, h]
  | ok mode =>
    have hp := cometS11_accepts_implies_pins anchor u hostNow mode h
    omega

/-- **`S11` CometBFT Falsifier 3 — Stale header (`hostNow > headerTime + maxStaleness`) is rejected.** -/
theorem cometS11_rejects_stale_header (anchor : CometTrustAnchor) (u : CometHeaderUpdate)
    (hostNow : Nat) (hstale : hostNow > u.headerTime + anchor.maxStaleness) :
    cometAccepted anchor u hostNow = false := by
  cases h : verifyCometHeaderS11 anchor u hostNow with
  | error _ => simp [cometAccepted, h]
  | ok mode =>
    have hp := cometS11_accepts_implies_pins anchor u hostNow mode h
    omega

/-- **`S11` CometBFT Falsifier 4 — Future timestamp spoof is rejected.** -/
theorem cometS11_rejects_future_time_spoof (anchor : CometTrustAnchor) (u : CometHeaderUpdate)
    (hostNow : Nat) (hf : u.headerTime > hostNow + anchor.maxClockDrift) :
    cometAccepted anchor u hostNow = false := by
  cases h : verifyCometHeaderS11 anchor u hostNow with
  | error _ => simp [cometAccepted, h]
  | ok mode =>
    have hp := cometS11_accepts_implies_pins anchor u hostNow mode h
    omega

/-- **`S11` CometBFT Falsifier 5 — Voting power `≤ 2/3` is rejected.** -/
theorem cometS11_rejects_insufficient_voting_power (anchor : CometTrustAnchor)
    (u : CometHeaderUpdate) (hostNow : Nat)
    (hlow : u.signedPower * 3 ≤ u.totalPower * 2) :
    cometAccepted anchor u hostNow = false := by
  cases h : verifyCometHeaderS11 anchor u hostNow with
  | error _ => simp [cometAccepted, h]
  | ok mode =>
    have hp := cometS11_accepts_implies_pins anchor u hostNow mode h
    omega

/-- **`S11` CometBFT Falsifier 6 — Zero-overlap non-adjacent skip is rejected.** -/
theorem cometS11_rejects_zero_overlap_skip (anchor : CometTrustAnchor) (u : CometHeaderUpdate)
    (hostNow : Nat) (hskip : anchor.trustedHeight + 1 < u.height)
    (hzero : u.trustedSignedPower = 0) :
    cometAccepted anchor u hostNow = false := by
  cases h : verifyCometHeaderS11 anchor u hostNow with
  | error _ => simp [cometAccepted, h]
  | ok mode =>
    have hp := cometS11_accepts_implies_pins anchor u hostNow mode h
    rcases hp.2.2.2.2.2.2.2.2.2.2.2 with ⟨_, hadj, _⟩ | ⟨_, _, _, hov⟩
    · omega
    · omega

/-! ## Part C: Premise Inhabitation Witnesses, Golden Vectors & `#tooth` Falsifiers -/

section WitnessesAndTeeth

private def demoFrustum : Frustum :=
  { viewer := "alice"
    visibleSlots := [("root", 0)]
    policy := fun c =>
      if c = "vault-secret" then .sever 0xBEEF
      else if c = "mock-oracle" then .interpose "cached-price"
      else if c = "shared-doc" then .attenuate [("shared-doc", 1)]
      else .tether }

private def demoTree : ViewNode :=
  .vstack (.cons (.bind 0 "public_balance" .amount none)
    (.cons (.host "vault-secret" .live (.some (.bind 7 "private_key_share" .hex none)))
      (.cons (.host "mock-oracle" .live (.some (.gauge 2 100 "oracle" none))) .nil)))

private def worldA : WorldState
  | "root", 0 => 1000
  | "vault-secret", 7 => 42
  | _, _ => 0

private def worldB : WorldState
  | "root", 0 => 1000
  | "vault-secret", 7 => 999999
  | _, _ => 0

private def worldVisibleChanged : WorldState
  | "root", 0 => 2500
  | "vault-secret", 7 => 42
  | _, _ => 0

/-- Concrete fog-of-war witness: mutating the `sever`ed secret slot `("vault-secret", 7)` from
`42` to `999999` leaves `projectViewNode` identical. -/
theorem witness_severed_secret_unchanged :
    projectViewNode demoFrustum worldA "root" demoTree =
      projectViewNode demoFrustum worldB "root" demoTree := by
  decide

/-- `#tooth` non-vacuity falsifier: mutating the visible slot `("root", 0)` from `1000` to `2500`
DOES change `projectViewNode` (proving the lens is nontrivial). -/
theorem tooth_visible_slot_mutation_changes_projection :
    projectViewNode demoFrustum worldA "root" demoTree ≠
      projectViewNode demoFrustum worldVisibleChanged "root" demoTree := by
  decide

/-- `#tooth` patch falsifier: applying a `VStack` container patch to a `Row` fails closed (`none`). -/
theorem tooth_applyPatch_mismatched_container_refused :
    applyPatch (.row (.cons (.text "a") .nil))
      (.patchContainer .vstack (.cons .keep .nil)) = none := rfl

/-- Concrete repair badge witness: missing capability produces exact missing list. -/
theorem witness_repair_badge_missing_cap :
    synthesizeRepairBadge "publish" ["cap.write", "cap.sign"] ["cap.write"] true none =
      ⟨"publish", "unauthorized: missing required capabilities", ["cap.sign"], none⟩ := rfl

/-- Golden Electra mainnet period-1800 anchor (shared identically with Rust `quarried_shells`).
`periodOfSlot 14745664 = 14745664 / 8192 = 1800`. -/
def goldenEthAnchor : EthTrustAnchor :=
  { expectedChainId := 1
    expectedForkDigest := 0x6A95A1A9
    currentPeriod := 1800
    trustedAttestedSlot := 14745600
    trustedFinalizedSlot := 14745536
    maxStaleness := 3600
    maxClockDrift := 60 }

/-- Golden Electra mainnet update with `397/512` participants and Electra depth-7 finality branch. -/
def goldenEthElectra397 : EthHeaderUpdate :=
  { chainId := 1
    forkDigest := 0x6A95A1A9
    attestedSlot := 14745664
    signatureSlot := 14745665
    finalizedSlot := 14745600
    attestedTime := 1780000000
    committeeLen := 512
    bitsLen := 512
    participantCount := 397
    blsAggOk := true
    finalityBranchLen := 7
    finalityBranchOk := true
    execBranchLen := 4
    execBranchOk := true }

def goldenEthHostNow : Nat := 1780000120

/-- Golden witness: Electra `397/512` mainnet-shape header is accepted. -/
theorem goldenEthElectra397_accepts :
    verifyEthHeaderS11 goldenEthAnchor goldenEthElectra397 goldenEthHostNow = .ok () := by
  decide

/-- Golden boundary witness: exact `342/512` supermajority floor is accepted. -/
theorem goldenEthElectra342_accepts :
    verifyEthHeaderS11 goldenEthAnchor { goldenEthElectra397 with participantCount := 342 }
      goldenEthHostNow = .ok () := by
  decide

/-- `#tooth` falsifier: `341/512` (one below `2/3`) is rejected with `insufficientParticipation`. -/
theorem tooth_goldenEth_341_rejected :
    verifyEthHeaderS11 goldenEthAnchor { goldenEthElectra397 with participantCount := 341 }
      goldenEthHostNow = .error .insufficientParticipation := by
  decide

/-- `#tooth` falsifier: Sepolia (`chainId = 11155111`) replay on mainnet anchor is rejected. -/
theorem tooth_goldenEth_crossChain_rejected :
    verifyEthHeaderS11 goldenEthAnchor { goldenEthElectra397 with chainId := 11155111 }
      goldenEthHostNow = .error .chainIdMismatch := by
  decide

/-- `#tooth` falsifier: future-slot spoof (`signatureSlot < attestedSlot`) is rejected. -/
theorem tooth_goldenEth_futureSlot_rejected :
    verifyEthHeaderS11 goldenEthAnchor { goldenEthElectra397 with signatureSlot := 14745663 }
      goldenEthHostNow = .error .futureSlotSpoof := by
  decide

/-- `#tooth` falsifier: expired staleness (`hostNow = attestedTime + 3601`) is rejected. -/
theorem tooth_goldenEth_stale_rejected :
    verifyEthHeaderS11 goldenEthAnchor goldenEthElectra397 (1780000000 + 3601) =
      .error .staleHeader := by
  decide

/-- Golden CometBFT `cosmoshub-4` anchor (shared identically with Rust `quarried_shells`). -/
def goldenCometAnchor : CometTrustAnchor :=
  { expectedChainId := "cosmoshub-4"
    expectedForkDigest := 0xC0540504
    trustedHeight := 26000000
    trustedHeaderTime := 1780000000
    trustingPeriod := 1209600
    maxStaleness := 3600
    maxClockDrift := 60 }

/-- Golden CometBFT adjacent header (`height = 26000001`). -/
def goldenCometAdjacent : CometHeaderUpdate :=
  { chainId := "cosmoshub-4"
    forkDigest := 0xC0540504
    height := 26000001
    headerTime := 1780000006
    epochBindOk := true
    selfBindOk := true
    commitMatchesHeader := true
    totalPower := 300
    signedPower := 201
    trustedTotalPower := 300
    trustedSignedPower := 201 }

/-- Golden CometBFT `95`-block skipping header (`height = 26000095`, `> 1/3` overlap). -/
def goldenCometSkip95 : CometHeaderUpdate :=
  { chainId := "cosmoshub-4"
    forkDigest := 0xC0540504
    height := 26000095
    headerTime := 1780000570
    epochBindOk := false
    selfBindOk := true
    commitMatchesHeader := true
    totalPower := 300
    signedPower := 240
    trustedTotalPower := 300
    trustedSignedPower := 101 }

theorem goldenCometAdjacent_accepts :
    verifyCometHeaderS11 goldenCometAnchor goldenCometAdjacent 1780000020 = .ok .adjacent := by
  decide

theorem goldenCometSkip95_accepts :
    verifyCometHeaderS11 goldenCometAnchor goldenCometSkip95 1780000600 = .ok .skipping := by
  decide

/-- `#tooth` falsifier: `theta-testnet-001` cross-chain replay is rejected. -/
theorem tooth_goldenComet_crossChain_rejected :
    verifyCometHeaderS11 goldenCometAnchor
      { goldenCometAdjacent with chainId := "theta-testnet-001" } 1780000020 =
      .error .chainIdMismatch := by
  decide

/-- `#tooth` falsifier: expired trusting period (`hostNow = trustedTime + 1209600`) is rejected. -/
theorem tooth_goldenComet_expiredTrustPeriod_rejected :
    verifyCometHeaderS11 goldenCometAnchor goldenCometAdjacent (1780000000 + 1209600) =
      .error .trustedStateExpired := by
  decide

/-- `#tooth` falsifier: exact `2/3` (`200/300`) voting power is rejected (strict `> 2/3` required). -/
theorem tooth_goldenComet_exactTwoThirds_rejected :
    verifyCometHeaderS11 goldenCometAnchor
      { goldenCometAdjacent with signedPower := 200 } 1780000020 =
      .error .insufficientVotingPower := by
  decide

/-- `#tooth` falsifier: zero-overlap `95`-block skip is rejected. -/
theorem tooth_goldenComet_zeroOverlapSkip_rejected :
    verifyCometHeaderS11 goldenCometAnchor
      { goldenCometSkip95 with trustedSignedPower := 0 } 1780000600 =
      .error .insufficientTrustOverlap := by
  decide

end WitnessesAndTeeth

/-! ## Part D: `#guard_msgs`-Pinned Axiom Audit -/

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.fog_of_war_viewNode_noninterference' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms fog_of_war_viewNode_noninterference

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.severed_secret_mutation_invisible' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms severed_secret_mutation_invisible

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.applyPatch_diff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyPatch_diff

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.ethS11_accepts_implies_pins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ethS11_accepts_implies_pins

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.ethS11_rejects_cross_chain_replay' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms ethS11_rejects_cross_chain_replay

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.ethS11_rejects_future_slot_spoof' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms ethS11_rejects_future_slot_spoof

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.ethS11_rejects_expired_staleness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ethS11_rejects_expired_staleness

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.cometS11_accepts_implies_pins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cometS11_accepts_implies_pins

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.cometS11_rejects_expired_trust_period' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cometS11_rejects_expired_trust_period

/-- info: 'Minidregg.Assurance.LightClientAndViewLens.cometS11_rejects_zero_overlap_skip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cometS11_rejects_zero_overlap_skip

end Minidregg.Assurance.LightClientAndViewLens
