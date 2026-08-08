/-
# `Kernel/TurnBalancedLimit.lean` — N2b: the turn INCLUDING conservation is a universal object.

SUBSTRATE: pure MODEL work in Lean — a category-theory keystone about the turn as a
universal object. No AIR, no constraints, no circuit emission anywhere in this file.

N2a (`Kernel/TurnLimit.lean`) proved the AGREEMENT half: at a fixed turn `t` the cone data
`HyperedgeConeData` is a wide-pullback limit. `Kernel/Turn.lean`'s `binding_is_proper`
shows `balanced` (the conservation aggregate `Σᵢ halfEdge i (x i) t = 0`) is NOT derivable
from that cone — it is a further condition. N2b makes the refinement itself universal:
`balanced` carves an EQUALIZER subobject of N2a's limit — the balanced cone data
`BalancedConeData` is the equalizer of the balance-sum map against the zero map in `Type u`,
with the genuine `IsLimit` universal property, and its inclusion into the agreement limit
is a monomorphism. So the conserving turn = the agreement limit ⊓ the balance equalizer,
each half a real universal property, composed in `balanced_turn_universal`.

Proved (genuine, no `sorry`, no vacuous obligation):
  * `balanceSum` / `balanceHom` / `zeroHom` — the parallel pair on the N2a limit object.
  * `BalancedConeData`   — N2b's object: the subtype of `HyperedgeConeData` where the sum is `0`.
  * `balancedFork`       — the fork whose point it is; `balanced_is_equalizer` — that fork IS
    a limit of `parallelPair balanceHom zeroHom` (mathlib `Types.type_equalizer_iff_unique`).
  * `balancedFork_ι_mono` — the inclusion is mono: `balanced` carves a SUBOBJECT.
  * `balanced_turn_universal` — the package: N2a's limit (REUSED verbatim, not re-derived)
    + the equalizer + the mono, in one statement.
  * the bridge: `BalancedConeData.toHyperedge` / `Hyperedge.toBalancedConeData` /
    `balancedConeData_iff_hyperedge` — the balanced cone data at `t` is inhabited exactly
    when a `Kernel/Turn.lean` `Hyperedge` with turn `t` exists. N2b's object IS the hyperedge.

Honest scope — what is proved vs. residual:
  * PROVED: the equalizer/subobject form. The balanced data has the equalizer's universal
    property over the agreement limit, and the agreement limit has the wide-pullback
    universal property (N2a). Conservation is seen by a universal object, which the plain
    N2a limit could not do.
  * [N2b-fibered] RESIDUAL (prose only — a `Prop := True` twin would be the vacuous-
    obligation anti-pattern): the single FUSED diagram — one shape category extending
    `WidePullbackShape ι` with a parallel pair into a `Bal` object, whose limit is
    `BalancedConeData` directly rather than as a two-stage limit-then-equalizer. It needs
    the augmented shape authored carefully (`N2-HYPEREDGE-LIMIT.md` §1's "get the category
    right" warning bites exactly there). The two-stage form proved here is not weaker in
    content — finite limits factor through products+equalizers — but the fused shape is the
    statement of record for "ONE diagram whose limit is the conserving turn".

Keystones BUILT below (the audit lesson: exhibit, never assert), at ONE concrete instance
`ι = Fin 2`, everything `ℤ`, `stepId`/`zeroRead` REUSED from `Kernel/TurnLimit.lean`,
`halfEdge = stateHalf` (each leg contributes its own pre-state): satisfiable — the +5/−5
transfer is agreeing AND balanced, and lifts to a full `Hyperedge`; teeth — at the SAME
instance, the (1,1) tuple is in the agreement limit but provably NOT in the equalizer
(so the subobject is proper AND inhabited — refinement, not vacuity), plus
`Hyperedge.binding_is_proper` reused in N2b vocabulary; premise-inhabitation — the balanced
data is nonempty and the parallel-pair diagram is a genuine functor.
-/
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Kernel.TurnLimit

namespace Minidregg.Kernel

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### The balance parallel pair on N2a's limit object, and its equalizer. -/

section Balanced

variable {ι : Type u} [Fintype ι]
variable {Carrier Turn TurnId Bal : Type u} [AddCommMonoid Bal]
variable (step : Carrier → Turn → Carrier)
variable (turnId : ι → Carrier → TurnId)
variable (halfEdge : ι → Carrier → Turn → Bal)

/-- **The balance-sum map on the agreement limit.** Each cone-data point (a tuple with a
common apex) is sent to its conservation aggregate `Σᵢ halfEdge i (xᵢ) t`. This is the map
`balanced` equalizes against zero — defined on N2a's limit object, because conservation is
a condition on cones the plain wide pullback cannot see. -/
def balanceSum (t : Turn) : HyperedgeConeData step turnId t → Bal :=
  fun p => Finset.univ.sum fun i => halfEdge i (p.1 i) t

/-- The balance-sum map as a morphism of `Type u`. -/
def balanceHom (t : Turn) : HyperedgeConeData step turnId t ⟶ Bal :=
  ↾(balanceSum step turnId halfEdge t)

/-- The constantly-`0` morphism the balance sum is equalized against. -/
def zeroHom (t : Turn) : HyperedgeConeData step turnId t ⟶ Bal :=
  ↾(fun _ => 0)

/-- **N2b's object — the balanced cone data.** The subtype of the agreement limit where the
conservation aggregate vanishes: exactly `Hyperedge`'s `(x, agree, balanced)` at fixed `t`
(the bridge below makes that identification a theorem). As a subtype of the N2a limit it is
literally "the agreement limit ∩ the balance equalizer". -/
def BalancedConeData (t : Turn) : Type u :=
  { p : HyperedgeConeData step turnId t // balanceSum step turnId halfEdge t p = 0 }

/-- **The balanced fork** — the equalizer candidate: `BalancedConeData` included into the
agreement limit, equalizing `balanceHom` with `zeroHom` (the inclusion commutes because
every balanced point sums to `0` by its defining property). -/
def balancedFork (t : Turn) :
    Fork (balanceHom step turnId halfEdge t) (zeroHom step turnId t) :=
  Fork.ofι
    (↾(Subtype.val : BalancedConeData step turnId halfEdge t → HyperedgeConeData step turnId t))
    (by ext p; exact p.2)

/-- **N2b, the equalizer half — the balanced cone data IS the equalizer of the balance sum
against zero.** `balancedFork` is a limit of `parallelPair balanceHom zeroHom`: every map
into the agreement limit whose composite balance sum vanishes factors UNIQUELY through the
balanced data. This is the universal property conservation adds on top of N2a — proved by
reusing mathlib's characterization of equalizers in `Type u`
(`Types.type_equalizer_iff_unique`), not re-derived. No `Nonempty ι` needed: the equalizer
is universal over the empty index too. -/
theorem balanced_is_equalizer (t : Turn) :
    Nonempty (IsLimit (balancedFork step turnId halfEdge t)) :=
  (Types.type_equalizer_iff_unique
      (f := ↾(Subtype.val :
        BalancedConeData step turnId halfEdge t → HyperedgeConeData step turnId t))
      (w := by ext p; exact p.2)).mpr
    fun p hp => ⟨⟨p, hp⟩, rfl, fun _ hq => Subtype.ext hq⟩

/-- **The inclusion is a monomorphism** — `balanced` carves a genuine SUBOBJECT of N2a's
agreement limit (mathlib's `mono_iff_injective` + subtype-inclusion injectivity). Properness
— that the subobject can be strict — is the teeth below, not asserted here. -/
theorem balancedFork_ι_mono (t : Turn) :
    Mono (balancedFork step turnId halfEdge t).ι :=
  (mono_iff_injective _).mpr fun _ _ h => Subtype.ext h

/-- **N2b — the turn INCLUDING conservation is a universal object.** The package, one
statement: at a fixed turn `t` over a nonempty index, (i) the agreement data is a
wide-pullback limit (N2a, `hyperedge_is_wide_pullback`, REUSED verbatim), (ii) the balanced
data is the equalizer of the balance sum against zero over that limit, and (iii) the
equalizer includes monomorphically — so the conserving turn is the subobject of the
universal agreement object carved by a second universal property, each half machine-checked.
The one-diagram fused form remains [N2b-fibered] (header). -/
theorem balanced_turn_universal [Nonempty ι] (t : Turn) :
    Nonempty (IsLimit (hyperedgeCone step turnId t))
      ∧ Nonempty (IsLimit (balancedFork step turnId halfEdge t))
      ∧ Mono (balancedFork step turnId halfEdge t).ι :=
  ⟨hyperedge_is_wide_pullback step turnId t,
   balanced_is_equalizer step turnId halfEdge t,
   balancedFork_ι_mono step turnId halfEdge t⟩

end Balanced

/-! ### The bridge — N2b's object IS `Kernel/Turn.lean`'s `Hyperedge` at fixed `t`. -/

section Bridge

variable {ι : Type u} [Fintype ι]
variable {Carrier Turn TurnId Bal : Type u} [AddCommMonoid Bal] [DecidableEq TurnId]
variable {step : Carrier → Turn → Carrier}
variable {turnId : ι → Carrier → TurnId}
variable {halfEdge : ι → Carrier → Turn → Bal}

/-- A balanced cone-data point yields the full `Hyperedge`: the tuple, the fixed turn, the
witnessed apex id, the cone condition, and — the N2b content — `balanced` discharged by the
equalizer membership. Noncomputable only through choosing the existential apex witness. -/
noncomputable def BalancedConeData.toHyperedge {t : Turn}
    (q : BalancedConeData step turnId halfEdge t) :
    Hyperedge ι Carrier Turn TurnId Bal step turnId halfEdge where
  x := q.1.1
  t := t
  tid := q.1.2.choose
  agree := q.1.2.choose_spec
  balanced := q.2

/-- Conversely, every `Hyperedge` is a balanced cone-data point at its own turn: `agree`
gives the existential apex, `balanced` gives the equalizer membership. -/
def Hyperedge.toBalancedConeData
    (H : Hyperedge ι Carrier Turn TurnId Bal step turnId halfEdge) :
    BalancedConeData step turnId halfEdge H.t :=
  ⟨⟨H.x, H.tid, H.agree⟩, H.balanced⟩

/-- **The identification** — the balanced cone data at `t` is inhabited exactly when a
`Hyperedge` with turn `t` exists. N2b's universal object is not a new notion of turn beside
`Kernel/Turn.lean`'s: it is the same object, now exhibited with its universal property. -/
theorem balancedConeData_iff_hyperedge (t : Turn) :
    Nonempty (BalancedConeData step turnId halfEdge t)
      ↔ Nonempty { H : Hyperedge ι Carrier Turn TurnId Bal step turnId halfEdge // H.t = t } := by
  constructor
  · rintro ⟨q⟩; exact ⟨q.toHyperedge, rfl⟩
  · rintro ⟨H, rfl⟩; exact ⟨H.toBalancedConeData⟩

end Bridge

/-! ### Keystone fields — BUILT witnesses at ONE concrete instance.

`ι = Fin 2`, `Carrier = Turn = TurnId = Bal = ℤ`, `stepId`/`zeroRead` reused from
`Kernel/TurnLimit.lean`, and ONE half-edge (`stateHalf`) under which the equalizer subobject
is simultaneously inhabited (satisfiable) and proper (teeth) — the strongest non-vacuity:
`balanced` genuinely refines the agreement limit, cutting away some points and keeping
others, at a single instance. -/

section Keystones

/-- Each leg contributes its own pre-state to the balance sum (the half-edge reads the
carrier). Under it, conservation is a REAL condition on tuples: some agree-ing tuples sum
to `0` and some do not. -/
def stateHalf : Fin 2 → ℤ → ℤ → ℤ := fun _ c _ => c

/-- The +δ/−δ transfer tuple at δ = 5: leg 0 holds `+5`, leg 1 holds `−5`. -/
def transferTuple : Fin 2 → ℤ := ![5, -5]

/-- The lopsided tuple: both legs hold `+1` — agreement holds, conservation cannot. -/
def lopTuple : Fin 2 → ℤ := ![1, 1]

/-- The transfer as a point of N2a's agreement limit (`zeroRead`: every leg reads apex `0`). -/
def transferPoint : HyperedgeConeData stepId zeroRead (0 : ℤ) :=
  ⟨transferTuple, 0, fun _ => rfl⟩

/-- The lopsided tuple is ALSO a point of the agreement limit — agreement does not see it. -/
def lopPoint : HyperedgeConeData stepId zeroRead (0 : ℤ) :=
  ⟨lopTuple, 0, fun _ => rfl⟩

/-! **satisfiable** — a concrete BALANCED hyperedge inhabits the equalizer. -/

/-- The transfer is balanced: `(+5) + (−5) = 0`, so `transferPoint` lies in the equalizer. -/
def transferBalanced : BalancedConeData stepId zeroRead stateHalf (0 : ℤ) :=
  ⟨transferPoint, by
    simp [balanceSum, stateHalf, transferPoint, transferTuple, Fin.sum_univ_two]⟩

/-- The balanced data is inhabited at the concrete instance. -/
theorem balancedConeData_inhabited :
    Nonempty (BalancedConeData stepId zeroRead stateHalf (0 : ℤ)) :=
  ⟨transferBalanced⟩

/-- The equalizer universal property, transferred to the concrete instance. -/
theorem balanced_is_equalizer_fin2 :
    Nonempty (IsLimit (balancedFork stepId zeroRead stateHalf (0 : ℤ))) :=
  balanced_is_equalizer stepId zeroRead stateHalf 0

/-- The transfer lifts through the bridge to a full `Kernel/Turn.lean` `Hyperedge` — the
satisfiable witness reaches all the way to the landed turn structure. -/
theorem transfer_hyperedge_exists :
    Nonempty (Hyperedge (Fin 2) ℤ ℤ ℤ ℤ stepId zeroRead stateHalf) :=
  ⟨transferBalanced.toHyperedge⟩

/-! **teeth** — `balanced` strictly refines the agreement limit, two-pronged. -/

/-- (a) At the SAME instance as the satisfiable witness: the lopsided point's balance sum is
`2 ≠ 0` — it is in N2a's agreement limit yet fails the equalizer condition. -/
theorem lopPoint_not_balanced :
    balanceSum stepId zeroRead stateHalf (0 : ℤ) lopPoint ≠ 0 := by
  simp [balanceSum, stateHalf, lopPoint, lopTuple, Fin.sum_univ_two]

/-- (a, packaged) No point of the balanced equalizer maps onto `lopPoint`: the subobject is
PROPER — with `transferBalanced` in it and `lopPoint` outside it, `balanced` genuinely
carves, neither empty nor everything. -/
theorem lopPoint_not_in_equalizer :
    ¬ ∃ q : BalancedConeData stepId zeroRead stateHalf (0 : ℤ), q.1 = lopPoint := by
  rintro ⟨⟨p, hp⟩, rfl⟩
  exact lopPoint_not_balanced hp

/-- (b) `Hyperedge.binding_is_proper` (from `Kernel/Turn.lean`) REUSED, recast in N2b's
vocabulary: there is an agreement-limit point whose balance sum is nonzero — the abstract
form of "a cone that does not factor through the conserving equalizer". -/
theorem binding_is_proper_in_limit :
    ∃ (step : ℤ → ℤ → ℤ) (turnId : Unit → ℤ → ℤ) (halfEdge : Unit → ℤ → ℤ → ℤ) (t : ℤ)
      (p : HyperedgeConeData step turnId t),
      balanceSum step turnId halfEdge t p ≠ 0 := by
  obtain ⟨x, t, tid, step, turnId, halfEdge, hagree, hbal⟩ := Hyperedge.binding_is_proper
  exact ⟨step, turnId, halfEdge, t, ⟨x, tid, hagree⟩, hbal⟩

/-! **premise-inhabitation** — the equalizer diagram is genuine and its object nonempty. -/

/-- The balanced data is nonempty (the premise the universal property quantifies over is
not vacuous). Same witness as satisfiable, stated as the premise-inhabitation field. -/
theorem balanced_premise_inhabited :
    Nonempty (BalancedConeData stepId zeroRead stateHalf (0 : ℤ)) :=
  balancedConeData_inhabited

/-- The parallel-pair diagram genuinely respects identities — a real functor law at the
concrete instance, not a stipulation. -/
theorem parallelPair_map_id (X : WalkingParallelPair) :
    (parallelPair (balanceHom stepId zeroRead stateHalf (0 : ℤ))
        (zeroHom stepId zeroRead (0 : ℤ))).map (𝟙 X) = 𝟙 _ :=
  (parallelPair _ _).map_id X

end Keystones

end Minidregg.Kernel
