/-
# Theory.EpistemicConsensus — fault-tolerant distributed knowledge by verification.

ATLAS §3 inventory item 5, ported from breadstuffs `Metatheory/EpistemicConsensus.lean`
(the Goubault–Kniazev–Ledent–Rajsbaum *Simplicial Models for the Epistemic Logic of
Faulty Agents*, arXiv:2311.01351, read through the verify/find seam of
`Theory/Knowledge.lean`). A Kripke frame with a Byzantine subset; single-agent
knowledge `Kᵢ`; distributed knowledge `D_B` of a group; and the one proposition that
makes verification Byzantine-proof.

## The point

`verified X w₀ ≜ fun _ => Discharged X.stmt w₀` is a CONSTANT proposition over worlds:
whether witness `w₀` discharges claim `X` is a fact of the witness and the verifier, not
of which global state obtains. So it survives *every* indistinguishability edge of
*every* agent in *every* frame — `Knows i (verified X w₀) w` collapses to
`Discharged X.stmt w₀` regardless of `Indist`, of who is `Faulty`, of `i`, and of `w`
(`knows_verified_iff_discharged`, `distKnows_verified_iff_discharged`,
`knows_verified_frame_independent`). That is the Byzantine-proofing trick: a discharged
claim is distributed knowledge of the honest group and no Byzantine subset can forge it
(`no_dist_knowledge_of_unrealizable`) or destroy it (`distKnows_mono_group`) — the
knowledge is funnelled through `Verify`, never through assertion. For a *world-dependent*
proposition none of this holds: the keystone frame below has an agent that knows `φ`
and one that does not.

## Changes from the ancestor (each deliberate)

* `Frame.Alive` is DROPPED: no ported theorem uses it (the ancestor's proofs never
  mention it either). `indist_refl` is kept — it is the one S5 law the proofs use.
* `honest_dist_knowledge_iff_holds` is renamed `holds_of_honest_distKnows_verified`:
  it was never an `iff` (one direction; the converse is
  `honest_distributed_knows_discharged` up to the witness).
* The ancestor's explicit premise `∀ i, Honest i → Indist i actual actual` on
  `honest_dist_knowledge_iff_holds` and `no_dist_knowledge_of_unrealizable` is
  dropped: it is an instance of the frame's own `indist_refl` field, so both
  theorems here are strictly stronger (fewer hypotheses, same conclusion).
* `verified` lives at the module namespace, not under `Frame` (it takes no frame).
* Added: the world- and frame-independence theorems named above, decidability
  instances for `Knows`/`DistKnows` over finite frames (so the keystones are
  COMPUTED by `decide`, not eyeballed), and the keystone verifier is
  `Verify p w := decide (p = 2 * w)` rather than `decide (p = w)` — with the latter
  every claim is realizable, so the unrealizable-claim tooth could not fire.

## Residuals (prose, not built)

* `[EPISTEMIC-common]` common knowledge / the finality floor `C_G`
  (breadstuffs `Authority/Epistemic.lean` `FinalityFloor`, `CommonAt`) — not ported.
* `[EPISTEMIC-threshold]` `CommonSecret.ThresholdFrame` / `DistKnowsGeK`
  (the threshold cliff/jump) — not ported.
* `[EPISTEMIC-uc]` the dynamic UC composition theorem (environments, simulators,
  computational indistinguishability) — only the static conjunction fragment
  `honest_dist_knowledge_composes` is here, as in the ancestor.
* `[EPISTEMIC-adjudication]` Disputation / OptimisticAdjudication — not ported.
-/
import Mathlib.Data.Fintype.Basic
import Theory.Knowledge

namespace Minidregg.Theory.EpistemicConsensus

open Minidregg.Theory

universe u v w

/-- A **proposition** is the set of worlds at which it holds (the valuation). -/
abbrev Prop' (Ω : Type u) := Ω → Prop

/-- An **epistemic frame with faulty agents** over worlds `Ω` and agents `ι`. -/
structure Frame (Ω : Type u) (ι : Type v) where
  /-- The actual/true world — the global state that really obtains. -/
  actual : Ω
  /-- Agent `i`'s indistinguishability relation `∼ᵢ` (the Kripke accessibility). -/
  Indist : ι → Ω → Ω → Prop
  /-- An agent can never distinguish a world from itself — the only S5 law used. -/
  indist_refl : ∀ (i : ι) (w : Ω), Indist i w w
  /-- The **Byzantine / faulty** subset of agents. -/
  Faulty : ι → Prop

namespace Frame

variable {Ω : Type u} {ι : Type v} (F : Frame Ω ι)

/-- An agent is **honest** when it is not Byzantine. -/
def Honest (i : ι) : Prop := ¬ F.Faulty i

/-- **`Knows i φ` at `w`** — the single-agent modality `Kᵢ`: `φ` holds at every world
`i` cannot tell apart from `w`. -/
def Knows (i : ι) (φ : Prop' Ω) (w : Ω) : Prop :=
  ∀ w', F.Indist i w' w → φ w'

/-- **`DistKnows B φ` at `w`** — distributed knowledge of group `B` (`D_B`): `φ` holds
at every world that *every* member of `B` confuses with `w`. The group pools its
perspectives: a world is excluded as soon as *some* member can tell it apart. -/
def DistKnows (B : ι → Prop) (φ : Prop' Ω) (w : Ω) : Prop :=
  ∀ w', (∀ i, B i → F.Indist i w' w) → φ w'

instance instDecidableHonest [∀ i, Decidable (F.Faulty i)] (i : ι) :
    Decidable (F.Honest i) :=
  inferInstanceAs (Decidable (¬ F.Faulty i))

/-- Over a finite world-set, knowledge is decidable: "does `i` know `φ`" is a
computation, which is what lets the keystones below be `decide`d. -/
instance instDecidableKnows [Fintype Ω] (i : ι) (φ : Prop' Ω) (w : Ω)
    [∀ w', Decidable (F.Indist i w' w)] [∀ w', Decidable (φ w')] :
    Decidable (F.Knows i φ w) :=
  inferInstanceAs (Decidable (∀ w', F.Indist i w' w → φ w'))

instance instDecidableDistKnows [Fintype Ω] [Fintype ι]
    (B : ι → Prop) [∀ i, Decidable (B i)] (φ : Prop' Ω) (w : Ω)
    [∀ i w', Decidable (F.Indist i w' w)] [∀ w', Decidable (φ w')] :
    Decidable (F.DistKnows B φ w) :=
  inferInstanceAs (Decidable (∀ w', (∀ i, B i → F.Indist i w' w) → φ w'))

end Frame

/-! ## §2. A discharged claim is a world-independent checkable fact -/

/-- The proposition *"witness `w₀` discharges claim `X`"*, as a world-set. It ignores
the world: it holds either at every world or at none. This is the formal content of
"a certificate is freely copyable / context-independent". -/
def verified {P W : Type w} [Verifiable P W] (X : Claim P) (w₀ : W) : Prop' Ω :=
  fun _ => Discharged (P := P) (W := W) X.stmt w₀

instance instDecidableVerified {Ω : Type u} {P W : Type w} [Verifiable P W]
    (X : Claim P) (w₀ : W) (w : Ω) : Decidable (verified (Ω := Ω) X w₀ w) :=
  inferInstanceAs (Decidable (Discharged (P := P) (W := W) X.stmt w₀))

/-- The trick, stated: `verified X w₀` does not depend on the world. (Definitional —
it IS the construction; the non-definitional consequences follow.) -/
theorem verified_world_independent {Ω : Type u} {P W : Type w} [Verifiable P W]
    (X : Claim P) (w₀ : W) (w w' : Ω) :
    verified (Ω := Ω) X w₀ w ↔ verified (Ω := Ω) X w₀ w' :=
  Iff.rfl

/-! ## §3. Fault-tolerant knowledge by verification — the keystones -/

namespace Frame

variable {Ω : Type u} {ι : Type v} (F : Frame Ω ι)

/-- **Every agent knows a discharged claim** — honest or Byzantine — because
`verified` survives every indistinguishability edge. -/
theorem all_know_discharged {P W : Type w} [Verifiable P W]
    (X : Claim P) (w₀ : W) (hd : Discharged (P := P) (W := W) X.stmt w₀) (i : ι) :
    F.Knows i (verified (Ω := Ω) X w₀) F.actual :=
  fun _ _ => hd

/-- **Knowledge of a verified claim is exactly its discharge**, at any world, for any
agent, in any frame. The `→` direction reads the constant off the reflexive edge
(`indist_refl`); the `←` direction needs nothing. -/
theorem knows_verified_iff_discharged {P W : Type w} [Verifiable P W]
    (X : Claim P) (w₀ : W) (i : ι) (w : Ω) :
    F.Knows i (verified (Ω := Ω) X w₀) w ↔ Discharged (P := P) (W := W) X.stmt w₀ :=
  ⟨fun h => h w (F.indist_refl i w), fun hd _ _ => hd⟩

/-- **Distributed knowledge of a verified claim is exactly its discharge**, for ANY
group `B` — in particular independent of which agents are `Faulty`. -/
theorem distKnows_verified_iff_discharged {P W : Type w} [Verifiable P W]
    (X : Claim P) (w₀ : W) (B : ι → Prop) (w : Ω) :
    F.DistKnows B (verified (Ω := Ω) X w₀) w ↔ Discharged (P := P) (W := W) X.stmt w₀ :=
  ⟨fun h => h w (fun i _ => F.indist_refl i w), fun hd _ _ => hd⟩

/-- **Frame-independence**: whether an agent knows a verified claim does not depend on
the frame (its `Indist`, its `Faulty`), the agent, or the world. Two arbitrary frames
over the same worlds and agents agree on every such knowledge question. -/
theorem knows_verified_frame_independent {P W : Type w} [Verifiable P W]
    (X : Claim P) (w₀ : W) (F₁ F₂ : Frame Ω ι) (i₁ i₂ : ι) (w₁ w₂ : Ω) :
    F₁.Knows i₁ (verified (Ω := Ω) X w₀) w₁ ↔ F₂.Knows i₂ (verified (Ω := Ω) X w₀) w₂ :=
  (F₁.knows_verified_iff_discharged X w₀ i₁ w₁).trans
    (F₂.knows_verified_iff_discharged X w₀ i₂ w₂).symm

/-- **The honest group has distributed knowledge of a discharged claim.** -/
theorem honest_distributed_knows_discharged {P W : Type w} [Verifiable P W]
    (X : Claim P) (w₀ : W) (hd : Discharged (P := P) (W := W) X.stmt w₀) :
    F.DistKnows F.Honest (verified (Ω := Ω) X w₀) F.actual :=
  fun _ _ => hd

/-- **Unforgeability**: the only way the honest group can have distributed knowledge
of `verified X w₀` is for `X` to actually be held (`w₀` discharges it). There is no
assertion channel a Byzantine subset could use to manufacture the knowledge.
(Ancestor: `honest_dist_knowledge_iff_holds`, which was this one direction with a
redundant reflexivity premise.) -/
theorem holds_of_honest_distKnows_verified {P W : Type w} [Verifiable P W]
    (X : Claim P) (w₀ : W)
    (hdk : F.DistKnows F.Honest (verified (Ω := Ω) X w₀) F.actual) :
    Holds (W := W) X :=
  ⟨w₀, (F.distKnows_verified_iff_discharged X w₀ F.Honest F.actual).mp hdk⟩

/-- **A larger group knows at least as much**: monotonicity in the group. Dually,
removing Byzantine agents never destroys knowledge the honest core already holds. -/
theorem distKnows_mono_group (B B' : ι → Prop) (hsub : ∀ i, B i → B' i)
    (φ : Prop' Ω) (w : Ω) (h : F.DistKnows B φ w) : F.DistKnows B' φ w :=
  fun w' hall => h w' (fun i hi => hall i (hsub i hi))

/-- **Single-agent knowledge entails group distributed knowledge.** The converse
fails (`Keystone.agent1_not_knows` with `Keystone.group_distKnows`). -/
theorem knows_imp_distKnows (B : ι → Prop) (i : ι) (hi : B i)
    (φ : Prop' Ω) (w : Ω) (h : F.Knows i φ w) : F.DistKnows B φ w :=
  fun w' hall => h w' (hall i hi)

/-- **An unrealizable claim is never distributed-known**: if no witness discharges
`X`, then for every offered `w₀` the honest group does not know `verified X w₀`. -/
theorem no_dist_knowledge_of_unrealizable {P W : Type w} [Verifiable P W]
    (X : Claim P) (w₀ : W) (hnh : ¬ Holds (W := W) X) :
    ¬ F.DistKnows F.Honest (verified (Ω := Ω) X w₀) F.actual :=
  fun hdk => hnh (F.holds_of_honest_distKnows_verified X w₀ hdk)

/-- **Static composition fragment**: honest distributed knowledge of two verified
claims pools into knowledge of their conjunction. The dynamic theorem is
`[EPISTEMIC-uc]`. -/
theorem honest_dist_knowledge_composes {P W : Type w} [Verifiable P W]
    (X Y : Claim P) (wx wy : W)
    (hX : F.DistKnows F.Honest (verified (Ω := Ω) X wx) F.actual)
    (hY : F.DistKnows F.Honest (verified (Ω := Ω) Y wy) F.actual) :
    F.DistKnows F.Honest
      (fun w => verified (Ω := Ω) X wx w ∧ verified (Ω := Ω) Y wy w) F.actual :=
  fun w' hall => ⟨hX w' hall, hY w' hall⟩

end Frame

/-! ## §4. Keystones — a discriminating frame, every fact COMPUTED.

Two worlds `Bool` (`true` actual), two agents `Fin 2`: agent `0` distinguishes the
worlds, agent `1` confuses them; agent `1` is Byzantine. The world-dependent
`φ := (· = true)` separates the modalities (satisfiable + teeth for `Knows` and
`DistKnows`); the verifier `p = 2 * w` gives a discharged claim (`⟨6⟩` by `3`), a wrong
witness (`⟨6⟩` by `4`), and an unrealizable claim (`⟨3⟩`, odd). -/

namespace Keystone

/-- The frame: agent `0` sees the world (`Indist 0 w w' ↔ w = w'`), agent `1` sees
nothing (`Indist 1 _ _` is always true); agent `1` is faulty. -/
def F : Frame Bool (Fin 2) where
  actual := true
  Indist := fun i w w' => i = 0 → w = w'
  indist_refl := fun _ _ _ => rfl
  Faulty := fun i => i = 1

instance (i : Fin 2) (w w' : Bool) : Decidable (F.Indist i w w') :=
  inferInstanceAs (Decidable (i = 0 → w = w'))

instance (i : Fin 2) : Decidable (F.Faulty i) :=
  inferInstanceAs (Decidable (i = 1))

/-- The world-dependent proposition: true exactly at the actual world. -/
def φ : Prop' Bool := fun w => w = true

instance (w : Bool) : Decidable (φ w) := inferInstanceAs (Decidable (w = true))

/-- The whole group. -/
def everyone : Fin 2 → Prop := fun _ => True

instance (i : Fin 2) : Decidable (everyone i) := inferInstanceAs (Decidable True)

/-- satisfiable (`Knows`): the seeing agent knows `φ`. -/
theorem agent0_knows : F.Knows 0 φ F.actual := by decide

/-- teeth (`Knows`): the blind agent does not — knowledge is a real constraint. -/
theorem agent1_not_knows : ¬ F.Knows 1 φ F.actual := by decide

/-- satisfiable (`DistKnows`): the whole group knows `φ` (through agent `0`). -/
theorem group_distKnows : F.DistKnows everyone φ F.actual := by decide

/-- teeth (`DistKnows`): the Byzantine subset `{1}` alone does not know `φ`. -/
theorem faulty_alone_not_distKnows : ¬ F.DistKnows F.Faulty φ F.actual := by decide

/-- The keystone verifier: `p` is discharged by `w` iff `p = 2 * w`. Local to this
namespace so no other `Verifiable ℕ ℕ` is ever shadowed. -/
local instance doubleVerifier : Verifiable ℕ ℕ := ⟨fun p w => decide (p = 2 * w)⟩

/-- A realizable claim (witness `3`). -/
def X : Claim ℕ := ⟨6⟩

/-- An unrealizable claim (odd; no `w` has `2 * w = 3`). -/
def Y : Claim ℕ := ⟨3⟩

theorem X_discharged_by_3 : Discharged (P := ℕ) (W := ℕ) X.stmt 3 := by decide

theorem X_not_discharged_by_4 : ¬ Discharged (P := ℕ) (W := ℕ) X.stmt 4 := by decide

theorem Y_unrealizable : ¬ Holds (W := ℕ) Y := by
  rintro ⟨w, hw⟩
  have h : 3 = 2 * w := of_decide_eq_true hw
  omega

/-- BOTH agents know the verified claim — including the blind, faulty agent `1`,
who does not know `φ` (`agent1_not_knows`). -/
theorem both_know_verified :
    F.Knows 0 (verified X 3) F.actual ∧ F.Knows 1 (verified X 3) F.actual := by
  decide

/-- The honest group has it as distributed knowledge. -/
theorem honest_distKnows_verified : F.DistKnows F.Honest (verified X 3) F.actual := by
  decide

/-- So does the Byzantine subset alone — the knowledge does not depend on who is
faulty (`distKnows_verified_iff_discharged`), unlike `faulty_alone_not_distKnows`. -/
theorem faulty_alone_distKnows_verified : F.DistKnows F.Faulty (verified X 3) F.actual := by
  decide

/-- A wrong witness is known by nobody, even though `X` is held (by `3`). -/
theorem nobody_knows_wrong_witness :
    ¬ F.Knows 0 (verified X 4) F.actual ∧ ¬ F.Knows 1 (verified X 4) F.actual := by
  decide

/-- The unrealizable claim is distributed-known by nobody for ANY offered witness —
`no_dist_knowledge_of_unrealizable` fires. -/
theorem nobody_distKnows_unrealizable (w₀ : ℕ) :
    ¬ F.DistKnows F.Honest (verified Y w₀) F.actual :=
  F.no_dist_knowledge_of_unrealizable Y w₀ Y_unrealizable

/-- The same at `w₀ := 4`, computed directly. -/
theorem nobody_distKnows_unrealizable_4 : ¬ F.DistKnows F.Honest (verified Y 4) F.actual := by
  decide

end Keystone

/-! ## §5. Axiom pins. -/

/-- info: 'Minidregg.Theory.EpistemicConsensus.Frame.all_know_discharged' does not depend on any axioms -/
#guard_msgs in #print axioms Frame.all_know_discharged

/-- info: 'Minidregg.Theory.EpistemicConsensus.Frame.knows_verified_iff_discharged' does not depend on any axioms -/
#guard_msgs in #print axioms Frame.knows_verified_iff_discharged

/-- info: 'Minidregg.Theory.EpistemicConsensus.Frame.distKnows_verified_iff_discharged' does not depend on any axioms -/
#guard_msgs in #print axioms Frame.distKnows_verified_iff_discharged

/-- info: 'Minidregg.Theory.EpistemicConsensus.Frame.knows_verified_frame_independent' does not depend on any axioms -/
#guard_msgs in #print axioms Frame.knows_verified_frame_independent

/-- info: 'Minidregg.Theory.EpistemicConsensus.Frame.holds_of_honest_distKnows_verified' does not depend on any axioms -/
#guard_msgs in #print axioms Frame.holds_of_honest_distKnows_verified

/-- info: 'Minidregg.Theory.EpistemicConsensus.Frame.distKnows_mono_group' does not depend on any axioms -/
#guard_msgs in #print axioms Frame.distKnows_mono_group

/-- info: 'Minidregg.Theory.EpistemicConsensus.Frame.no_dist_knowledge_of_unrealizable' does not depend on any axioms -/
#guard_msgs in #print axioms Frame.no_dist_knowledge_of_unrealizable

/-- info: 'Minidregg.Theory.EpistemicConsensus.Frame.honest_dist_knowledge_composes' does not depend on any axioms -/
#guard_msgs in #print axioms Frame.honest_dist_knowledge_composes

/-- info: 'Minidregg.Theory.EpistemicConsensus.Keystone.agent1_not_knows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Keystone.agent1_not_knows

/--
info: 'Minidregg.Theory.EpistemicConsensus.Keystone.group_distKnows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Keystone.group_distKnows

/--
info: 'Minidregg.Theory.EpistemicConsensus.Keystone.faulty_alone_not_distKnows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Keystone.faulty_alone_not_distKnows

/-- info: 'Minidregg.Theory.EpistemicConsensus.Keystone.both_know_verified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Keystone.both_know_verified

/-- info: 'Minidregg.Theory.EpistemicConsensus.Keystone.Y_unrealizable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Keystone.Y_unrealizable

/-- info: 'Minidregg.Theory.EpistemicConsensus.Keystone.nobody_distKnows_unrealizable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Keystone.nobody_distKnows_unrealizable

end Minidregg.Theory.EpistemicConsensus
