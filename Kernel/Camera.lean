/-
# Kernel.Camera — the four-substance product resource algebra (the camera tier).

PORT, not new mathematics. Ground truth transcribed from breadstuffs:

  * `metatheory/Dregg2/Resource.lean` — the discrete resource algebra
    (`ResourceAlgebra`, an Iris camera without step-indexing), the
    frame-preserving update `Fpu`, and the three carrier cameras: `ℕ` (the
    sum-conservation bridge), `Excl` (NFT/linear tokens), `Auth`
    (authoritative ↔ fragment, the sovereign split).
  * `metatheory/Metatheory/Dynamics/Substance.lean` — the four-substance
    signature, the product camera instance, the product glue `fpu_prod`, the
    product tooth `not_fpu_prod_left`, and the two keystones
    `authority_evidence_share_camera` / `value_no_free_copy`.

The paper2 substance table (`paper2/01-model.md §1.2`) is what this algebra
mechanizes: value **linear** (moves, never copies or vanishes; per-asset Σδ = 0),
authority **produced under non-forgeability** (*only connectivity begets
connectivity*), evidence **monotone** (once known, never unknown), state
**guarded-mutable** (the frame rule). Every kernel verb passes two gates —
admission (epistemic: `Verify P w`, `Theory/Knowledge.lean`) and footprint
(ontic: a frame-preserving update in THIS product camera). This file is the
footprint half's algebra.

Discipline added in the port (ATLAS §6 law 2 — a keystone that can't exhibit
both poles doesn't compile): every keystone carries, BESIDE it, a concrete
camera where its `Fpu` genuinely fires AND a hostile update genuinely refused —
named satisfiability witnesses, anonymous `example` teeth (the Loom
convention). Axiom pins are `#guard_msgs in #print axioms` (self-verifying;
minidregg has no `#assert_axioms` yet — that tool is Assurance-lane territory).

Deliberately NOT here: N1's substance *classification* (`docs/KERNEL-NECESSITY.md
§N1` — exhaustiveness / "no fourth substance" is statement territory for the
design owners). This file lands the objects that classification will quantify
over. Also not here: `camera_blind_to_caveats` and `Verb = admission ×
footprint-Fpu` (`VerbSignature.lean`), which arrive with the verbs.
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs

namespace Minidregg.Kernel

universe u v w x

/-! ## §1. The resource algebra (Iris camera, discrete).

`Dregg2/Resource.lean:61-96`. A monoid measure ("a quantity that adds") cannot
express resources whose very *composition is partial* — NFTs/linear tokens (two
holders of one unique id compose INVALIDLY, not additively), fractional
permissions (shares compose only while ≤ 1), authoritative ↔ fragment (a
holder's view `◦ f` is valid only within the sovereign total `● a`). The
unifying structure is Iris's camera (Jung et al., *Iris from the Ground Up*,
JFP 2018): a partial commutative monoid with a validity predicate and a partial
`core` for the duplicable part. Ghost state and permissions live in ONE
algebra, so conservation and authority unify. -/

/-- **A resource algebra (Iris camera, discrete/simplified).** A partial
commutative monoid: `op` is the composition `·`, `valid` carves out the
admissible elements (the partiality), `core` extracts the duplicable/persistent
part (`none` = nothing persistent). No unit is required (cameras need not be
unital). Port of `Dregg2/Resource.lean:71-92`. -/
class ResourceAlgebra (R : Type u) where
  /-- Composition `a · b` (defined everywhere; partiality is carried by `valid`). -/
  op    : R → R → R
  /-- The validity predicate — the heart of partiality (NFT disjointness, frac `≤ 1`). -/
  valid : R → Prop
  /-- The core `|a|` — the part of `a` that may be freely duplicated; `none` = none. -/
  core  : R → Option R
  /-- `·` is commutative. -/
  op_comm  : ∀ a b, op a b = op b a
  /-- `·` is associative. -/
  op_assoc : ∀ a b c, op (op a b) c = op a (op b c)
  /-- Validity is downward-closed under composition: a valid composite has valid parts
  (Iris camera axiom — you cannot manufacture validity by adding a frame). -/
  valid_op_left : ∀ a b, valid (op a b) → valid a
  /-- **core-id** (`|a| · a = a`): the core is a left-identity for its own element. -/
  core_id : ∀ a ca, core a = some ca → op ca a = a
  /-- **core-idem** (`||a|| = |a|`): the core is idempotent. -/
  core_idem : ∀ a ca, core a = some ca → core ca = some ca
  /-- **core-mono** (`a ≼ b → |a| ≼ |b|`): the core is monotone along the extension
  order `≼` (`a ≼ b ≜ ∃ c, b = a · c`). -/
  core_mono : ∀ a b ca, core a = some ca → (∃ c, b = op a c) →
                ∃ cb, core b = some cb ∧ ∃ d, cb = op ca d

namespace ResourceAlgebra
@[inherit_doc] scoped infixl:70 " ⊙ " => ResourceAlgebra.op
end ResourceAlgebra

open ResourceAlgebra

/-- **The frame-preserving update** `a ↝ b`: replacing `a` by `b` keeps every
frame `f` that was compatible with `a` compatible with `b`. THIS is the general
conservation law; "the global sum is preserved" is its `(ℕ,+)` shadow. Every
kernel verb's footprint half is an `Fpu` in the product camera (paper2
§1.2 "two gates"). Port of `Dregg2/Resource.lean:103-104`. -/
def Fpu {R : Type u} [ResourceAlgebra R] (a b : R) : Prop :=
  ∀ f : R, valid (a ⊙ f) → valid (b ⊙ f)

/-- `↝` is reflexive: doing nothing is frame-preserving. (`Resource.lean:114`.) -/
theorem Fpu.refl {R : Type u} [ResourceAlgebra R] (a : R) : Fpu a a :=
  fun _ h => h

/-- `↝` is transitive. (`Resource.lean:118`.) -/
theorem Fpu.trans {R : Type u} [ResourceAlgebra R] {a b c : R}
    (hab : Fpu a b) (hbc : Fpu b c) : Fpu a c :=
  fun f h => hbc f (hab f h)

/-- In a total, always-valid camera *every* update is frame-preserving: there
are no third-party constraints to break. The non-triviality of conservation
lives entirely in `valid` — which is why the richer cameras below (`Excl`,
`Auth`) are where the law bites. (`Resource.lean:144-146`.) -/
theorem fpu_of_total {R : Type u} [ResourceAlgebra R]
    (htotal : ∀ x : R, valid x) (a b : R) : Fpu a b :=
  fun f _ => htotal (b ⊙ f)

/-! ## §2. Carrier camera 1 — `ℕ` under `+`: the sum-conservation bridge.

`Dregg2/Resource.lean:122-138`. This is bare sum-conservation ("Σδ = 0", the
paper2 value row's shadow) seen as a resource algebra: everything valid, core
the duplicable unit `0`. It exists here mostly as the DEGENERATE pole — by
`fpu_of_total` every update fires, so it also serves the teeth below as the
camera in which copying is NOT refused (the refusals are Excl/Auth content, not
tautologies of all cameras). -/

instance : ResourceAlgebra Nat where
  op    := (· + ·)
  valid := fun _ => True
  core  := fun _ => some 0
  op_comm  := Nat.add_comm
  op_assoc := Nat.add_assoc
  valid_op_left := fun _ _ _ => trivial
  core_id := by rintro a ca h; rw [Option.some.injEq] at h; subst h; exact Nat.zero_add a
  core_idem := by intro a ca h; exact h
  core_mono := by
    rintro a b ca h _; rw [Option.some.injEq] at h; subst h
    exact ⟨0, rfl, 0, (Nat.add_zero 0).symm⟩

/-! ## §3. Carrier camera 2 — `Excl`: the exclusive (NFT / linear-token) camera.

`Dregg2/Resource.lean:148-186`. `ex a` is held by exactly one party; two `ex`
never compose, which is precisely **non-duplication** — the structural fact
behind NFTs and Move's linear resources. There is no "amount": the conserved
content is *unique existence*. This is the paper2 value row ("linear — moves,
never copies or vanishes") at the camera tier. -/

/-- The exclusive camera carrier: a held unique value, or the invalidity bottom. -/
inductive Excl (R : Type u) : Type u where
  | ex : R → Excl R
  | invalid
  deriving Repr

/-- Composition of exclusives: any composition of two held values is `invalid`
(you cannot hold the same unique resource twice); `invalid` is absorbing. -/
def Excl.op {R : Type u} : Excl R → Excl R → Excl R
  | _, _ => Excl.invalid

/-- An exclusive is valid iff it is an actually-held value (never `invalid`). -/
def Excl.valid {R : Type u} : Excl R → Prop
  | .ex _    => True
  | .invalid => False

instance {R : Type u} : ResourceAlgebra (Excl R) where
  op    := Excl.op
  valid := Excl.valid
  core  := fun _ => none          -- nothing exclusive is duplicable: empty core
  op_comm  := by intro a b; rfl   -- both sides are `invalid`
  op_assoc := by intro a b c; rfl -- all compositions collapse to `invalid`
  -- `op a b = invalid` is never `valid`, so the hypothesis is vacuous.
  valid_op_left := by intro a b h; exact absurd h (by simp [Excl.op, Excl.valid])
  -- the empty core (`none`) makes all three core laws vacuously true.
  core_id := by intro a ca h; simp at h
  core_idem := by intro a ca h; simp at h
  core_mono := by intro a b ca h _; simp at h

/-- **Non-duplication, proved.** No exclusive resource composes with itself
validly — the camera-level statement that an NFT cannot be in two places.
(`Resource.lean:185-186`.) -/
theorem excl_no_dup {R : Type u} (a : Excl R) : ¬ valid (a ⊙ a) := by
  simp [ResourceAlgebra.op, ResourceAlgebra.valid, Excl.op, Excl.valid]

/-! ## §4. Carrier camera 3 — `Auth`: authoritative ↔ fragment (the sovereign split).

`Dregg2/Resource.lean:188-310`. **This is where conservation and authority
become the same law.** A sovereign cell holds the **authoritative** total
`● a : M`; each holder holds a **fragment** `◦ f : M`, valid only when `f ≼ a`
(the fragment fits within the authority). The authoritative slot is exclusive
(two `●` never compose), fragments add. "The sum is conserved" is precisely
"the authoritative total is preserved while fragments rearrange within it" —
an `Fpu` on `Auth M`. Per the paper2 table this ONE camera carries BOTH the
authority row and the evidence row — the keystone in §6 proves that. -/

section Auth

variable {M : Type u} [AddCommMonoid M]

/-- Monoid **extension order**: `fits f a` iff `a = f + c` for some remainder
`c` — the fragment `f` fits within the authority `a` (no order typeclass
needed; the monoid generates its own `≼`). (`Resource.lean:205`.) -/
def fits (f a : M) : Prop := ∃ c, a = f + c

/-- The authoritative↔fragment carrier: an optional authoritative total plus an
owned fragment, or the invalidity bottom (reached by composing two
authoritatives). (`Resource.lean:209-212`.) -/
inductive Auth (M : Type u) where
  | mk (auth : Option M) (frag : M)
  | invalid

/-- Composition: fragments add; at most one authoritative may be present (two ⇒
`invalid`); `invalid` is absorbing. -/
def Auth.op : Auth M → Auth M → Auth M
  | .invalid, _ => .invalid
  | _, .invalid => .invalid
  | .mk a1 f1, .mk a2 f2 =>
      match a1, a2 with
      | none,   a       => .mk a (f1 + f2)
      | a,      none    => .mk a (f1 + f2)
      | some _, some _  => .invalid

/-- Validity: `invalid` is never valid; a pure fragment is always valid; an
authoritative element is valid iff its fragment fits within its total. -/
def Auth.valid : Auth M → Prop
  | .invalid       => False
  | .mk none _     => True
  | .mk (some a) f => fits f a

instance : ResourceAlgebra (Auth M) where
  op    := Auth.op
  valid := Auth.valid
  core  := fun _ => some (.mk none 0)   -- the empty fragment: the duplicable unit
  op_comm  := by
    intro a b
    cases a with
    | invalid => cases b <;> rfl
    | mk a1 f1 =>
      cases b with
      | invalid => rfl
      | mk a2 f2 =>
        cases a1 <;> cases a2 <;> simp [Auth.op, add_comm]
  op_assoc := by
    intro a b c
    cases a with
    | invalid => rfl
    | mk a1 f1 =>
      cases b with
      | invalid => cases c <;> rfl
      | mk a2 f2 =>
        cases c with
        | invalid => cases a1 <;> cases a2 <;> rfl
        | mk a3 f3 =>
          cases a1 <;> cases a2 <;> cases a3 <;>
            simp [Auth.op, add_assoc]
  valid_op_left := by
    intro a b h
    cases a with
    | invalid => exact absurd h (by cases b <;> simp [Auth.op, Auth.valid])
    | mk a1 f1 =>
      cases b with
      | invalid => exact absurd h (by simp [Auth.op, Auth.valid])
      | mk a2 f2 =>
        cases a1 with
        | none => simp [Auth.valid]
        | some a1 =>
          cases a2 with
          | none =>
            -- op = mk (some a1) (f1+f2), valid means fits (f1+f2) a1
            simp only [Auth.op, Auth.valid, fits] at h ⊢
            obtain ⟨c, hc⟩ := h
            exact ⟨f2 + c, by rw [hc, add_assoc]⟩
          | some a2 =>
            -- op = invalid, h : False
            exact absurd h (by simp [Auth.op, Auth.valid])
  core_id := by
    intro a ca h
    rw [Option.some.injEq] at h; subst h
    cases a with
    | invalid => rfl
    | mk a1 f1 =>
      cases a1 <;> simp [Auth.op, zero_add]
  core_idem := by intro a ca h; rw [Option.some.injEq] at h; subst h; rfl
  core_mono := by
    intro a b ca h _
    rw [Option.some.injEq] at h; subst h
    exact ⟨.mk none 0, rfl, .mk none 0, by simp [Auth.op, add_zero]⟩

/-- **CANONICAL conservation law: conservation = a frame-preserving update on
the authoritative camera.** Moving a holder's fragment `f → f'` under a *fixed*
sovereign total `a` is frame-preserving exactly when it does not enlarge what
any frame needs (`hmono`). This is the statement the bare-sum law hides: a
*withdrawal* (`f' ≼ f`) is always conservative; a *deposit* is conservative
only against the authority's headroom. "Σ in = Σ out" is the special case
where `hmono` holds by an exact swap. (`Resource.lean:296-310`.) -/
theorem conservation_is_fpu (a f f' : M)
    (hmono : ∀ g, fits (f + g) a → fits (f' + g) a) :
    Fpu (R := Auth M) (.mk (some a) f) (.mk (some a) f') := by
  intro fr h
  cases fr with
  | invalid => exact absurd h (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid])
  | mk a2 f2 =>
    cases a2 with
    | none =>
      -- op (mk (some a) f) (mk none f2) = mk (some a) (f + f2); valid = fits (f + f2) a
      simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid] at h ⊢
      exact hmono f2 h
    | some a2 =>
      -- both authoritative ⇒ op = invalid ⇒ h : False
      exact absurd h (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid])

/-- **Authoritative growth is `Fpu`** (the EVIDENCE law — Iris
`auth_update_auth`). Enlarging the authoritative element `● a` to `● (a + t)`
while fragments stand still never invalidates a frame: every fragment that fit
within `a` fits within `a + t`. THIS is the monotone-substance law — "once
known, never unknown" (paper2 evidence row) as a camera fact.
(`Metatheory/Dynamics/Substance.lean:186-198`.) -/
theorem auth_grow_fpu (a t f : M) :
    Fpu (R := Auth M) (.mk (some a) f) (.mk (some (a + t)) f) := by
  intro fr hv
  cases fr with
  | invalid =>
    exact absurd hv (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid])
  | mk a2 g =>
    cases a2 with
    | none =>
      simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits] at hv ⊢
      obtain ⟨c, hc⟩ := hv
      exact ⟨c + t, by rw [hc, add_assoc]⟩
    | some a2 =>
      exact absurd hv (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid])

end Auth

/-! ## §5. The product of resource algebras IS a resource algebra.

`Metatheory/Dynamics/Substance.lean:79-159` (itself mirroring
`Dregg2/Substrate/FpuProbe.instProdRA` — same construction, not new
mathematics). Componentwise `op`/`valid`; the core exists iff both components'
cores exist (the Iris product-camera `pcore`). This is what makes "four
substances, one algebra" literal: a verb's footprint is ONE `Fpu` in the
product, and a violation in ANY single substance kills the whole verb. -/

instance instProdRA {A : Type u} {B : Type v} [ResourceAlgebra A] [ResourceAlgebra B] :
    ResourceAlgebra (A × B) where
  op a b    := (a.1 ⊙ b.1, a.2 ⊙ b.2)
  valid a   := valid a.1 ∧ valid a.2
  core a    :=
    match core a.1, core a.2 with
    | some c1, some c2 => some (c1, c2)
    | _, _ => none
  op_comm a b := by
    show (a.1 ⊙ b.1, a.2 ⊙ b.2) = (b.1 ⊙ a.1, b.2 ⊙ a.2)
    rw [op_comm a.1 b.1, op_comm a.2 b.2]
  op_assoc a b c := by
    show ((a.1 ⊙ b.1) ⊙ c.1, (a.2 ⊙ b.2) ⊙ c.2) = (a.1 ⊙ (b.1 ⊙ c.1), a.2 ⊙ (b.2 ⊙ c.2))
    rw [op_assoc a.1 b.1 c.1, op_assoc a.2 b.2 c.2]
  valid_op_left a b h := ⟨valid_op_left a.1 b.1 h.1, valid_op_left a.2 b.2 h.2⟩
  core_id a ca h := by
    cases h1 : core a.1 with
    | none => simp [h1] at h
    | some c1 =>
      cases h2 : core a.2 with
      | none => simp [h1, h2] at h
      | some c2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        show (c1 ⊙ a.1, c2 ⊙ a.2) = a
        rw [core_id a.1 c1 h1, core_id a.2 c2 h2]
  core_idem a ca h := by
    cases h1 : core a.1 with
    | none => simp [h1] at h
    | some c1 =>
      cases h2 : core a.2 with
      | none => simp [h1, h2] at h
      | some c2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        show (match core c1, core c2 with
              | some d1, some d2 => some (d1, d2)
              | _, _ => none) = some (c1, c2)
        rw [core_idem a.1 c1 h1, core_idem a.2 c2 h2]
  core_mono a b ca h hext := by
    cases h1 : core a.1 with
    | none => simp [h1] at h
    | some c1 =>
      cases h2 : core a.2 with
      | none => simp [h1, h2] at h
      | some c2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        obtain ⟨e, he⟩ := hext
        have hb1 : ∃ z, b.1 = a.1 ⊙ z := ⟨e.1, by rw [he]⟩
        have hb2 : ∃ z, b.2 = a.2 ⊙ z := ⟨e.2, by rw [he]⟩
        obtain ⟨d1, hd1, w1, hw1⟩ := core_mono a.1 b.1 c1 h1 hb1
        obtain ⟨d2, hd2, w2, hw2⟩ := core_mono a.2 b.2 c2 h2 hb2
        refine ⟨(d1, d2), by rw [hd1, hd2], (w1, w2), ?_⟩
        show (d1, d2) = (c1 ⊙ w1, c2 ⊙ w2)
        rw [hw1, hw2]

/-- **The product glue** (`Substance.lean:144-149`, mirroring
`FpuProbe.fpu_prod`). Componentwise `Fpu` lifts to the product — the formal
content of "one theorem schema over the product of the substances." -/
theorem fpu_prod {A : Type u} {B : Type v} [ResourceAlgebra A] [ResourceAlgebra B]
    {a b : A} {c d : B} (h1 : Fpu a b) (h2 : Fpu c d) : Fpu (a, c) (b, d) :=
  fun f hv => ⟨h1 f.1 hv.1, h2 f.2 hv.2⟩

/-- **The product tooth** (`Substance.lean:151-159`, mirroring
`FpuProbe.not_fpu_prod_left`). If ONE component update is not `Fpu` (witnessed
by a frame the other component can accompany validly), the PRODUCT update is
not `Fpu` — a violation in any single substance kills the whole verb. This is
the non-vacuity backbone: the product schema inherits every corner's tooth. -/
theorem not_fpu_prod_left {A : Type u} {B : Type v} [ResourceAlgebra A] [ResourceAlgebra B]
    {a b : A} {c d : B} (f1 : A)
    (hpre : ResourceAlgebra.valid (a ⊙ f1)) (hpost : ¬ ResourceAlgebra.valid (b ⊙ f1))
    (f2 : B) (hc : ResourceAlgebra.valid (c ⊙ f2)) : ¬ Fpu (a, c) (b, d) :=
  fun h => hpost (h (f1, f2) ⟨hpre, hc⟩).1

/-! ### §5(w). Witnesses: the product camera is non-degenerate; the glue and
the tooth both fire on concrete cameras. -/

/-- Satisfiability: the product camera has genuinely valid elements … -/
example : ResourceAlgebra.valid ((.mk none 1 : Auth ℕ), (3 : ℕ)) :=
  ⟨trivial, trivial⟩

/-- … and genuinely invalid ones (`valid` is not `⊤` — the camera can refuse). -/
example : ¬ ResourceAlgebra.valid ((Auth.invalid : Auth ℕ), (3 : ℕ)) :=
  fun h => h.1

/-- **`fpu_prod` fires** on a product where validity genuinely bites: a
withdrawal `◦2 → ◦1` under fixed sovereign total `●2` in `Auth ℕ` (a real
`hmono`, not a total camera), paired with an untouched `ℕ` component. -/
theorem fpu_prod_fires :
    Fpu (R := Auth ℕ × ℕ) (.mk (some 2) 2, 7) (.mk (some 2) 1, 7) :=
  fpu_prod
    (conservation_is_fpu 2 2 1 (by
      intro g hg
      obtain ⟨c, hc⟩ := hg
      exact ⟨1 + c, by omega⟩))
    (Fpu.refl 7)

/-- **`not_fpu_prod_left` fires**: forging a fragment out of thin air
(`◦0 → ◦2` with no authority backing it) in the LEFT substance kills the whole
product verb — even though the RIGHT component's update (`7 → 0` in the total
`ℕ` camera) is unimpeachably `Fpu`. The refusing frame is a sovereign `●1`
whose headroom the forged fragment overflows. -/
example : ¬ Fpu (R := Auth ℕ × ℕ) (.mk none 0, 7) (.mk none 2, 0) :=
  not_fpu_prod_left (.mk (some 1) 0)
    (by
      simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits]
      exact ⟨1, by omega⟩)
    (by
      simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits]
      rintro ⟨c, hc⟩
      omega)
    0 trivial

/-! ## §6. The four-substance signature and its keystones.

`Metatheory/Dynamics/Substance.lean:47-77` and `:164-242`. The four carriers —
value `V`, authority `A`, evidence `E`, state `S` — are each an abstract
resource algebra; the signature bundles ONLY the camera structure. The
disciplines (paper2 §1.2 rows) are theorems *about* `Fpu` in these cameras. -/

/-- **The four-substance signature**, candidate-independent
(`Substance.lean:55-68`). The disciplines are theorems about `Fpu` in the four
cameras, discharged for a concrete system by a candidate model — NOT
`RecordKernelState` field equations. The product camera (`instProdRA`) is what
a turn's footprint inhabits; `SubstanceProduct` names it. -/
structure Substances (V : Type u) (A : Type v) (E : Type w) (S : Type x)
    [ResourceAlgebra V] [ResourceAlgebra A] [ResourceAlgebra E] [ResourceAlgebra S] where
  /-- A witness that the signature is inhabited (a genesis product element). Keeps the
  structure non-empty without fixing a carrier — the candidate model supplies a real one. -/
  genesis : V × A × E × S

/-- The product camera of the four substances — `value × authority × evidence ×
state`. A turn's footprint is a frame-preserving update *here*
(`Substance.lean:70-77`, there named `Product`; renamed to avoid squatting on
a bare `Product` in the kernel namespace). -/
abbrev SubstanceProduct (V : Type u) (A : Type v) (E : Type w) (S : Type x)
    [ResourceAlgebra V] [ResourceAlgebra A] [ResourceAlgebra E] [ResourceAlgebra S] :
    Type (max (max u v) (max w x)) :=
  V × A × E × S

/-- Satisfiability: the signature is inhabited at concrete cameras matching the
paper2 table — value exclusive (`Excl`), authority AND evidence the same `Auth`
functor at different monoids (the §6(a) keystone makes that literal), state as
`Excl` pending its guarded camera (the guard algebra arrives with `Pred/`). -/
example : Substances (Excl Unit) (Auth ℕ) (Auth ℕ) (Excl Unit) :=
  ⟨(.ex (), .mk none 0, .mk none 0, .ex ())⟩

/-! ### §6(a). Keystone: authority ≡ evidence — the SAME camera.

Breadstuffs' sharpest finding (`FpuProbe §F6`, made structural in
`Substance.lean:169-224`): authority (non-amplification) and evidence (monotone
growth) are two faces of ONE camera. The paper2 table's authority and evidence
rows are not analogous laws of sibling algebras; they are two theorems of
`Auth M`. -/

section Keystones

variable {M : Type u} [AddCommMonoid M]

/-- **`authority_evidence_share_camera` — the structural unification
(`Substance.lean:200-221`), PROVED, kernel-clean.** Over ANY `AddCommMonoid M`,
the authority discipline and the evidence discipline are laws of **one and the
same** camera `Auth M`:

  * the **AUTHORITY** law — a fragment minted *within* the bound is `Fpu`
    (non-amplifying production: granting `f → f'` under a fixed total `a`
    whenever `f'` covers no more than `f` does) — is `conservation_is_fpu`;
  * the **EVIDENCE** law — authoritative *growth* `● a → ● (a + t)` is `Fpu`
    (monotone: once `● a` is known, the knowledge only enlarges) — is
    `auth_grow_fpu`.

Both inhabit the SAME `Auth M`. This is not a coincidence observed of one
candidate; it is a *property of the signature*: the authority and evidence
carriers are constructed by the same `Auth (·)` functor, so the
non-amplification and monotone laws are two theorems of one algebra. (The
breadstuffs candidate model picks `M := USet Rights` for authority and
`M := USet Nat` for evidence.) -/
theorem authority_evidence_share_camera (a f f' : M)
    (hmono : ∀ g, fits (f + g) a → fits (f' + g) a) (t : M) :
    -- AUTHORITY: non-amplifying fragment production is Fpu in `Auth M` …
    Fpu (R := Auth M) (.mk (some a) f) (.mk (some a) f')
    -- … and EVIDENCE: authoritative growth is Fpu in the SAME `Auth M`.
    ∧ Fpu (R := Auth M) (.mk (some a) f) (.mk (some (a + t)) f) :=
  ⟨conservation_is_fpu a f f' hmono, auth_grow_fpu a t f⟩

end Keystones

/-! #### §6(a) witnesses — both laws FIRE and both laws REFUSE, concretely.

The breadstuffs original states the unification but carries its poles in a
separate probe file; here they sit beside the keystone (ATLAS §6 law 2). Four
concrete facts in `Auth ℕ`: each law demonstrated by a genuine update, each
law's characteristic VIOLATION refused by a genuine frame. -/

/-- AUTHORITY fires: both conjuncts of the keystone, instantiated — withdrawal
`◦2 → ◦1` under `●2` AND growth `●2 → ●5` — with a real `hmono` (the `g = 0`
headroom argument, not vacuous: `fits (2+g) 2` forces `g = 0`). -/
theorem authority_evidence_witness :
    Fpu (R := Auth ℕ) (.mk (some 2) 2) (.mk (some 2) 1)
    ∧ Fpu (R := Auth ℕ) (.mk (some 2) 2) (.mk (some (2 + 3)) 2) :=
  authority_evidence_share_camera 2 2 1
    (by
      intro g hg
      obtain ⟨c, hc⟩ := hg
      exact ⟨1 + c, by omega⟩)
    3

/-- AUTHORITY refuses (the non-amplification tooth): a fragment CANNOT
self-amplify past the sovereign total — `◦0 → ◦2` under `●1` is not `Fpu`. The
refuting frame is the sovereign `●1` itself: it tolerated `◦0` and cannot
tolerate `◦2`. "Only connectivity begets connectivity" (paper2 authority row)
at the camera tier. -/
example : ¬ Fpu (R := Auth ℕ) (.mk (some 1) 0) (.mk (some 1) 2) := by
  intro h
  have hv := h (.mk none 0) (by
    simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits]
    exact ⟨1, by omega⟩)
  simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits] at hv
  obtain ⟨c, hc⟩ := hv
  omega

/-- EVIDENCE refuses (the monotonicity tooth): knowledge cannot SHRINK —
`●2 → ●1` is not `Fpu`, because a holder's outstanding fragment `◦2` fit
within `●2` and does not fit within `●1`. "Once known, never unknown" (paper2
evidence row) has a converse with teeth: un-knowing breaks frames. -/
example : ¬ Fpu (R := Auth ℕ) (.mk (some 2) 0) (.mk (some 1) 0) := by
  intro h
  have hv := h (.mk none 2) (by
    simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits]
    exact ⟨0, by omega⟩)
  simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits] at hv
  obtain ⟨c, hc⟩ := hv
  omega

/-! ### §6(b). Keystone: value — the linear discipline bites. -/

/-- **`value_no_free_copy` — the linear discipline of value, PROVED,
kernel-clean** (`Substance.lean:226-240`). In the exclusive (NFT/linear-token)
value camera `Excl R`, no resource composes with itself validly: a unique value
cannot be in two places. This is the camera-level "moves, never copies" (paper2
value row) — the substructural skeleton of the value substance. (Mirrors
`excl_no_dup` under the substance name; the per-asset Σδ=0 ledger case is a
candidate model's obligation, not this signature's.) -/
theorem value_no_free_copy {R : Type u} (a : Excl R) : ¬ ResourceAlgebra.valid (a ⊙ a) :=
  excl_no_dup a

/-! #### §6(b) witnesses — the refusal is about REAL resources, and it is
Excl-content, not a triviality of all cameras. -/

/-- Satisfiability: the value camera has genuinely valid (held) elements — the
no-copy tooth below refuses compositions of REAL resources, not inhabitants of
an empty validity. -/
example : ResourceAlgebra.valid (Excl.ex ()) := trivial

/-- The tooth fires on a concrete held token: this unique value cannot be in
two places. -/
example : ¬ ResourceAlgebra.valid (Excl.ex () ⊙ Excl.ex ()) :=
  value_no_free_copy _

/-- The hostile contrast: in the total `ℕ` camera the "same" duplication IS
valid — `value_no_free_copy` is a genuine property of the exclusive camera,
not a tautology every camera satisfies. (The linear discipline is a CHOICE of
carrier; the keystone's content is that `Excl` enforces it.) -/
example : ResourceAlgebra.valid ((2 : ℕ) ⊙ (2 : ℕ)) := trivial

/-! ## §7. Axiom pins.

Kernel-clean is `⊆ {propext, Classical.choice, Quot.sound}`; these guards are
exact-output pins (stronger than the subset assert breadstuffs' `#assert_axioms`
made, and self-verifying: the build fails if a proof change alters the axiom
footprint). -/

/-- info: 'Minidregg.Kernel.fpu_prod' depends on axioms: [propext] -/
#guard_msgs in #print axioms fpu_prod

/-- info: 'Minidregg.Kernel.not_fpu_prod_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms not_fpu_prod_left

/-- info: 'Minidregg.Kernel.authority_evidence_share_camera' depends on axioms: [propext] -/
#guard_msgs in #print axioms authority_evidence_share_camera

/-- info: 'Minidregg.Kernel.value_no_free_copy' depends on axioms: [propext] -/
#guard_msgs in #print axioms value_no_free_copy

/-! ## §Coda.

The signature `Substances V A E S` carries the four abstract substance cameras;
the product camera (`instProdRA` / `fpu_prod` / `not_fpu_prod_left`) is where a
turn's footprint lives. The disciplines are abstract camera laws: authority and
evidence are PROVED one camera (`authority_evidence_share_camera`), value's
linearity bites (`value_no_free_copy`) — each with both poles exhibited beside
it. What comes NEXT (not here): `Verb = admission × footprint-Fpu` and
`camera_blind_to_caveats` (the pair is irreducible) with the verbs; the N1
classification ("no fourth substance") quantifies over the disciplines this
file lands (`docs/KERNEL-NECESSITY.md §N1`). -/

end Minidregg.Kernel
