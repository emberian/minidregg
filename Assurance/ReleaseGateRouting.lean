/-
# `Assurance/ReleaseGateRouting.lean` — the release-gate routing lemma and its binding control

**The wound this names** (an external handoff on "learn/infer-only" private computation). A host
can homomorphically compute ANY function over a private state `s`, and a release service reveals
one designated output bit of any resulting ciphertext. The host computes "put private bit 37
into the designated output position", submits it, reads the bit; `n` submissions read all of
`s`. This is NOT a break of the encryption — the encryption held at every step. It is an
UNBOUND release gate: the gate accepted a predicate without evidence that the predicate was the
AUTHORIZED transition. Both halves are theorems here:

* **§1 the routing lemma** (generic). A predicate-submission gate `gate : (S → Bool) → Bool`
  that accepts the coordinate projections — a fortiori one that accepts everything — makes the
  released bits DETERMINE the state. `determines_iff_separates` is the sharp form (the released
  bits determine `s` iff the accepted class separates points); `routing_of_projections` /
  `routing_of_accept_all` are the two instances; `hostReconstruct_exact` is the attack as a
  program. The falsifier when the class is too small: a gate accepting at most ONE predicate
  cannot determine a state of two or more bits (`single_predicate_not_determining`, pigeonhole),
  pinned on `Fin 2 → Bool` (`single_gate_two_states_one_bit`, `decide`).
* **§2 the binding control.** `BindingGate R stateOf outOf gate`: acceptance implies the released
  output stands in the authorized relation `R` to the evidence's state. When `R`'s outputs are a
  function of the PUBLIC projection alone (`PublicOnly`), the routing substitution is REFUSED
  (`routing_refused`: evidence whose output is not the authorized function of its public half is
  rejected, whatever its private half, whatever its proof string), and the released output cannot
  separate states agreeing publicly (`binding_release_public_only` — the gate-level twin of
  `Kernel/PrivateTurn`'s `privateTurn_public_indistinguishable`: there the VIEW is blind to the
  witness, here the RELEASE is). Concrete instance on `Fin 2 → Bool` — coordinate 0 designated,
  coordinate 1 private — every fact `decide` (`TwoBit`).
* **§3 the tree.** (i) `Kernel/PrivateEscrowSettlement`'s `EvidenceBinding.Acceptable` is the
  kernel-level gate shape: acceptance pins a NAMED relation — a nonzero proof-suite identity, or
  a declared MPC with nonzero protocol and federation (`acceptable_pins_named_relation`); the
  kernel's own routing refusal is `note_or_bfv_zero_suite_not_acceptable` (zero-pinned evidence
  is not acceptable, whatever it claims). And the kernel's `Settlement` is a `BindingGate` by
  TYPE: its `claimBound` field forces `releasedBase = fill.base` (`settlement_is_binding_gate`,
  `settlement_release_public_only` — the generic lemma applied to the real kernel type). (ii)
  `Compiler/CommittedTerminalFiatShamir`'s Stage-0 receipt (`FsReceipt`, 4,131 wires, 13 rounds)
  inhabits the evidence type. What it binds is exactly `descriptorHolds evmAddDescriptor (traceOf
  word)` with the root the word itself (`stage0_relation_is_descriptor`, `Iff.rfl`); the
  descriptor FORCES the released `Z` from the public `(X, Y)` (`stage0_released_output_forced`,
  through `evmAddDescriptor_means_semantics` and `fragment_run_eq_iff`), so the ideal Stage-0
  gate is a `BindingGate` (`stage0IdealGate_binding`) and refuses every routed `Z`
  (`stage0_routing_refused`); the deployed `fsCheck` reflects into the tree's `fiatShamir`, which
  accepts a statement outside the relation with probability `≤ (t + 14) · 4160/p^6` in the ROM
  (`stage0Receipt_is_bound_evidence` = `fsCheck_ok_fiatShamir` ∧ `stage0Receipt_price`).

**What the Stage-0 receipt binds, and does NOT.** It binds the DESCRIPTOR (`evmAddDescriptor`,
the authorized transition) and the FULL WORD — the public prefix `encodeBoundary X Y Z`
included — under the ideal commitment (`Stage0Exhibit.S = idealCommitment`: the root IS the
word). It does not hide anything: the whole word is in the Fiat–Shamir statement
(`stage0_statement_carries_word`, `rfl`), read in full by `gateVerify` and hashed by the oracle.
At Stage 0 there is no private half at all; "bound" here means "the released `Z` is the wrapped
sum of the operands the statement names, or the receipt is refused (up to the price)".

**Residuals, named.**
* `[RELEASE-hiding]` — the receipt binds, it does not hide. A gate that is bound AND hiding
  needs the word out of the statement (the `[CT-merkle-profile]` / `[FS-BCS]` route: only a root
  hashed, binding then load-bearing under `[COMMIT-CR]`) and a hiding argument on top
  (`Assurance/PrivateTurn`'s masked openings; `[ZK-RBR-game]`). Nothing here claims it.
* `[RELEASE-continuity]` — a bound gate does not prevent replaying a stale but valid state:
  `R s s' o` says nothing about `s` being CURRENT, and a gate that is a function of the evidence
  alone accepts a replay exactly as it accepted the original. The tree's continuity objects are
  `Kernel/DurableDataIntent`'s `StableNullifier`, `Kernel/DurableCommitProtocol`'s
  `Intent.nullifiersFreshCheck` (inside `preflight`), `Kernel/PrivateEscrowSettlement`'s
  `Settlement.installed_rekey_nullifier_not_fresh` and `Claim.computationNullifier`, and
  `Kernel/State`'s `UKey.nullifier` plane. None is re-proved here.
-/
import Kernel.PrivateEscrowSettlement
import Compiler.CommittedTerminalFiatShamir

namespace Minidregg.Assurance.ReleaseGateRouting

set_option autoImplicit false

/-! ## §1. The routing lemma -/

section Routing

variable {S : Type}

/-- A predicate-submission release gate: given a submitted predicate `f` (the "designated
bit" as a function of the private state), decides whether `f s` is revealed. -/
abbrev PredicateGate (S : Type) := (S → Bool) → Bool

/-- What the host learns about `s` through `gate`: for each accepted `f`, the bit `f s`. -/
def releasedView (gate : PredicateGate S) (s : S) : (S → Bool) → Option Bool :=
  fun f => if gate f then some (f s) else none

/-- **The released bits determine the state**: two states agreeing on every accepted
predicate are equal. -/
def Determines (gate : PredicateGate S) : Prop :=
  ∀ s t : S, (∀ f, gate f = true → f s = f t) → s = t

/-- The released views agree exactly when every accepted predicate agrees — so `Determines`
is literally "the released view is injective in the state". -/
theorem releasedView_eq_iff (gate : PredicateGate S) (s t : S) :
    releasedView gate s = releasedView gate t ↔ ∀ f, gate f = true → f s = f t := by
  constructor
  · intro h f hf
    have := congrFun h f
    simpa [releasedView, hf] using this
  · intro h
    funext f
    by_cases hf : gate f = true
    · simp [releasedView, hf, h f hf]
    · simp [releasedView, hf]

/-- The accepted class separates points. -/
def Separates (gate : PredicateGate S) : Prop :=
  ∀ s t : S, s ≠ t → ∃ f, gate f = true ∧ f s ≠ f t

/-- **The sharp routing lemma**: the released bits determine the state iff the accepted
class separates points. Everything below is an instance of one direction or the other. -/
theorem determines_iff_separates (gate : PredicateGate S) :
    Determines gate ↔ Separates gate := by
  constructor
  · intro hdet s t hst
    by_contra hno
    exact hst (hdet s t fun f hf => by_contra fun hne => hno ⟨f, hf, hne⟩)
  · intro hsep s t hview
    by_contra hst
    obtain ⟨f, hf, hne⟩ := hsep s t hst
    exact hne (hview f hf)

/-- The coordinate projections of an `n`-bit private state. -/
def proj (n : ℕ) (i : Fin n) : (Fin n → Bool) → Bool := fun s => s i

/-- **Routing (projections)**: a gate accepting every coordinate projection determines the
state — the released bits ARE the state, one submission per coordinate. -/
theorem routing_of_projections {n : ℕ} (gate : PredicateGate (Fin n → Bool))
    (h : ∀ i, gate (proj n i) = true) : Determines gate :=
  fun _ _ hview => funext fun i => hview (proj n i) (h i)

/-- **Routing (accept-all)**: the gate that reveals any submitted predicate — the handoff's
"release service reveals the designated output bit of any resulting ciphertext". -/
theorem routing_of_accept_all {n : ℕ} (gate : PredicateGate (Fin n → Bool))
    (h : ∀ f, gate f = true) : Determines gate :=
  routing_of_projections gate fun i => h (proj n i)

/-- **The attack as a program**: against a release service `reveal` that answers every
submitted predicate on the private state (`reveal f = f s`), `n` submissions — "put bit `i`
into the designated output position" — reconstruct `s`. -/
def hostReconstruct (n : ℕ) (reveal : ((Fin n → Bool) → Bool) → Bool) : Fin n → Bool :=
  fun i => reveal (proj n i)

theorem hostReconstruct_exact {n : ℕ} (s : Fin n → Bool) :
    hostReconstruct n (fun f => f s) = s := rfl

/-- **premise-inhabitation** — a gate accepting every projection exists (the accept-all gate),
so `routing_of_projections` is not about an empty premise; and on it the routing lemma fires. -/
theorem accept_all_gate_exists (n : ℕ) :
    ∃ gate : PredicateGate (Fin n → Bool), (∀ i, gate (proj n i) = true) ∧ Determines gate :=
  ⟨fun _ => true, fun _ => rfl, routing_of_accept_all _ fun _ => rfl⟩

/-- **Falsifier (class too small)**: a gate accepting at most ONE predicate reveals at most one
bit — it cannot determine a state of two or more bits (pigeonhole: `2^n` states, two bit
values). The routing lemma's premise — the projections are accepted — is load-bearing. -/
theorem single_predicate_not_determining {n : ℕ} (hn : 2 ≤ n)
    (gate : PredicateGate (Fin n → Bool)) (f₀ : (Fin n → Bool) → Bool)
    (hsingle : ∀ f, gate f = true → f = f₀) : ¬ Determines gate := by
  intro hdet
  have hcard : Fintype.card Bool < Fintype.card (Fin n → Bool) := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨s, t, hst, hbit⟩ := Fintype.exists_ne_map_eq_of_card_lt f₀ hcard
  exact hst (hdet s t fun f hf => by rw [hsingle f hf]; exact hbit)

/-- The one-predicate gate: reveal `f s` only for `f = f₀`. -/
def singleGate [DecidableEq (S → Bool)] (f₀ : S → Bool) : PredicateGate S :=
  fun f => decide (f = f₀)

theorem singleGate_accepts_only [DecidableEq (S → Bool)] (f₀ f : S → Bool)
    (h : singleGate f₀ f = true) : f = f₀ :=
  of_decide_eq_true h

/-- **Pinned on two bits**: the gate revealing only coordinate 0 accepts that projection
(satisfiable), yet the two DISTINCT states `![true, true]` and `![true, false]` present the SAME
released bit — so it does not determine the state; while the accept-all gate on the same
carrier does (the contrast, both poles on one instance). -/
theorem single_gate_two_states_one_bit :
    singleGate (proj 2 0) (proj 2 0) = true ∧
      (![true, true] : Fin 2 → Bool) ≠ ![true, false] ∧
      proj 2 0 ![true, true] = proj 2 0 ![true, false] ∧
      ¬ Determines (singleGate (proj 2 0)) ∧
      Determines (fun _ => true : PredicateGate (Fin 2 → Bool)) :=
  ⟨decide_eq_true rfl, by decide, rfl,
    single_predicate_not_determining (le_refl 2) _ _ (singleGate_accepts_only _),
    routing_of_accept_all _ fun _ => rfl⟩

end Routing

/-! ## §2. The binding control -/

section Binding

/-- An authorized relation: (state, next state, released output). -/
abbrev AuthorizedRelation (S O : Type) := S → S → O → Prop

/-- **A binding gate**: acceptance of evidence `e` implies its released output stands in the
authorized relation to its state. Evidence is neutral data until the gate decides; what
acceptance CERTIFIES is `R`. The proof string, if any, lives inside `E` — the gate reads it,
the statement does not mention it. -/
def BindingGate {E S O : Type} (R : AuthorizedRelation S O)
    (stateOf : E → S) (outOf : E → O) (gate : E → Bool) : Prop :=
  ∀ e, gate e = true → ∃ s', R (stateOf e) s' (outOf e)

/-- `R`'s released outputs are a fixed function `h` of the PUBLIC projection `π` of the state —
the designated output reads nothing but the public half. -/
def PublicOnly {S O Pub : Type} (R : AuthorizedRelation S O) (π : S → Pub) (h : Pub → O) :
    Prop :=
  ∀ s s' o, R s s' o → o = h (π s)

/-- **Routing refused**: under a binding gate for a public-only relation, evidence whose output
is not the authorized function of its public half is rejected — whatever its private half,
whatever its proof string. "output := private coordinate `i`" is refused at every state where
that coordinate differs from the designated output. -/
theorem routing_refused {E S O Pub : Type} {R : AuthorizedRelation S O} {π : S → Pub}
    {h : Pub → O} {stateOf : E → S} {outOf : E → O} {gate : E → Bool}
    (hbind : BindingGate R stateOf outOf gate) (hpub : PublicOnly R π h)
    (e : E) (hne : outOf e ≠ h (π (stateOf e))) : gate e = false := by
  by_contra hacc
  obtain ⟨_, hs'⟩ := hbind e (by simpa using hacc)
  exact hne (hpub _ _ _ hs')

/-- **Released outputs are public-only**: two accepted pieces of evidence whose states agree
publicly release the SAME output. The gate-level twin of
`Kernel.privateTurn_public_indistinguishable` (there the public VIEW is blind to the witness;
here the RELEASE is). The private half leaves no trace in what is released — which is exactly
the routing lemma's premise failing: the accepted class does not separate privately-differing
states. -/
theorem binding_release_public_only {E S O Pub : Type} {R : AuthorizedRelation S O}
    {π : S → Pub} {h : Pub → O} {stateOf : E → S} {outOf : E → O} {gate : E → Bool}
    (hbind : BindingGate R stateOf outOf gate) (hpub : PublicOnly R π h)
    (e e' : E) (he : gate e = true) (he' : gate e' = true)
    (hπ : π (stateOf e) = π (stateOf e')) : outOf e = outOf e' := by
  obtain ⟨_, h1⟩ := hbind e he
  obtain ⟨_, h2⟩ := hbind e' he'
  rw [hpub _ _ _ h1, hpub _ _ _ h2, hπ]

/-! ### The concrete instance — two bits, coordinate 0 designated, coordinate 1 private -/

namespace TwoBit

/-- Evidence in the model: a state and a claimed released output. Here the gate IS the
relation's decider, so no proof string is carried; the Stage-0 instance (§3) carries one. -/
structure Evidence (S O : Type) where
  state : S
  out : O

/-- The authorized relation: release coordinate 0; the next state is the state (a read). -/
def R : AuthorizedRelation (Fin 2 → Bool) Bool := fun s s' o => s' = s ∧ o = s 0

/-- The gate: decide the relation. -/
def gate (e : Evidence (Fin 2 → Bool) Bool) : Bool := decide (e.out = e.state 0)

/-- **premise-inhabitation** — the concrete gate IS a binding gate for `R`. -/
theorem gate_binding : BindingGate R Evidence.state Evidence.out gate :=
  fun e h => ⟨e.state, rfl, of_decide_eq_true h⟩

theorem R_publicOnly : PublicOnly R (fun s => s 0) id := fun _ _ _ h => h.2

/-- The routing substitution: at state `![false, true]`, submit "output := s 1" (the private
coordinate, which reads `true`). -/
def routed : Evidence (Fin 2 → Bool) Bool := ⟨![false, true], ![false, true] 1⟩

/-- **teeth** — the routed submission is refused, through the generic `routing_refused` at the
concrete instance (the side condition — the private coordinate differs from the designated
output at this state — is `decide`). -/
theorem routed_refused : gate routed = false :=
  routing_refused gate_binding R_publicOnly routed (by decide)

/-- The honest release at the same state: "output := s 0". -/
def honest : Evidence (Fin 2 → Bool) Bool := ⟨![false, true], false⟩

/-- **satisfiable** — the honest release is accepted. -/
theorem honest_accepted : gate honest = true := by decide

/-- **teeth, the other pole** — the private coordinate is not released: two states differing
ONLY at coordinate 1 are both accepted with the SAME output. On this carrier the accept-all
predicate gate would determine the state (`single_gate_two_states_one_bit`); the binding gate
releases coordinate 0 and nothing else. -/
theorem private_bit_not_released :
    gate ⟨![false, true], false⟩ = true ∧ gate ⟨![false, false], false⟩ = true ∧
      (![false, true] : Fin 2 → Bool) 1 ≠ ![false, false] 1 := by
  decide

end TwoBit

end Binding

/-! ## §3. The tree -/

/-! ### (i) The kernel gate shape — `Kernel/PrivateEscrowSettlement` -/

section Kernel

open Minidregg.Kernel.PrivateEscrowSettlement
open Minidregg.Kernel.CanonicalEscrowMarket (Fill)
open Minidregg.Theory.TypedAuthorization (Digest Portal AuthState)

/-- **The kernel's gate is binding-shaped**: `EvidenceBinding.Acceptable` pins a NAMED relation —
a nonzero proof-suite identity for a semantic proof, or a declared MPC with nonzero protocol
and federation and zero proof pins. The zero-pinned NoteSpend/BFV statements are refused
(`note_or_bfv_zero_suite_not_acceptable`): the kernel's own routing refusal. -/
theorem acceptable_pins_named_relation (b : EvidenceBinding) (h : b.Acceptable) :
    b.pins.proofSuiteId ≠ ⟨0⟩ ∨
      (b.mode = .sharedMpc ∧ b.pins = .zero ∧ b.protocolId ≠ ⟨0⟩ ∧ b.federationId ≠ ⟨0⟩) := by
  rcases h with hs | hm
  · exact Or.inl (b.semanticAssigned hs).1
  · exact Or.inr (b.mpcShape hm)

variable {Source : Claim → EvidenceBinding → Type}
  {M : Minidregg.Theory.CellState.Materializer
    Minidregg.Theory.CanonicalResourceKernel.schema Digest}
  {portal : Portal} {authState : AuthState}

/-- **The kernel's `Settlement` is a `BindingGate` by TYPE**: every settlement is accepted (the
gate is `claimBound`, a proof field — ill-typed until discharged), and its released base is
FORCED equal to the authorized public fill's base. The generic definition instantiated at the
real kernel type, not a mirror. Premise-inhabitation of the evidence type is the tree's
`Assurance/PrivateEscrowSettlementJoin`'s `Witness.settlement_nonempty` (not imported here). -/
theorem settlement_is_binding_gate :
    BindingGate (E := Settlement Source M portal authState)
      (fun (fill : Fill M portal authState) _ o => o = fill.base)
      (fun st => st.fill) (fun st => st.sealed.claim.releasedBase) (fun _ => true) :=
  fun st _ => ⟨st.fill, st.claimBound.releaseExact⟩

/-- **The kernel's released base is public-only**: two settlements over fills of the same base
release the same base — whatever their sealed private computations. `binding_release_public_only`
at the kernel. -/
theorem settlement_release_public_only (st₁ st₂ : Settlement Source M portal authState)
    (h : st₁.fill.base = st₂.fill.base) :
    st₁.sealed.claim.releasedBase = st₂.sealed.claim.releasedBase :=
  binding_release_public_only (π := fun fill : Fill M portal authState => fill.base) (h := id)
    settlement_is_binding_gate (fun _ _ _ ho => ho) st₁ st₂ rfl rfl h

end Kernel

/-! ### (ii) The Stage-0 receipt — `Compiler/CommittedTerminalFiatShamir` -/

section Stage0

open Minidregg.Compiler Minidregg.Compiler.EvmAddAir Minidregg.Compiler.DescriptorEval
open Minidregg.Compiler.CommittedTerminalRealizer (traceOf bitCorner residualEmbedding)
open Minidregg.Compiler.CommittedTerminalFiatShamir
open Minidregg.Selvage

-- `S` (the ideal commitment: the root IS the word), `wordOf` (the candidate array as a word),
-- `stage0_residuals_fit` (`N ≤ 2^13`) from the realizer's Stage-0 exhibit; `O` (the deployed
-- cSHAKE256 oracle over the encoded transcript prefix) from the Fiat–Shamir file's.
open Minidregg.Compiler.CommittedTerminalRealizer.Stage0Exhibit (S wordOf stage0_residuals_fit)
open Minidregg.Compiler.CommittedTerminalFiatShamir.Stage0Exhibit (O)

/-- The Stage-0 gate protocol as the tree's `Reduction`, at the ideal commitment. -/
noncomputable abbrev stage0Reduction :=
  gateReduction S.commit evmAddDescriptor (bitCorner 13) (by norm_num : 0 < 4131)

/-- **What the receipt binds, definitionally**: the source relation of the Stage-0 reduction
is "the root is the word and `evmAddDescriptor` holds on the word" — the authorized transition
and nothing else. `Iff.rfl`. -/
theorem stage0_relation_is_descriptor (rt y : Fin 4131 → BabyBear) :
    stage0Reduction.R () rt y () ↔ (y = rt ∧ descriptorHolds evmAddDescriptor (traceOf y)) :=
  Iff.rfl

/-- **The whole word is in the statement** — `[RELEASE-hiding]`: the Fiat–Shamir statement of a
carried receipt carries the entire 4,131-wire word as its implicit instance and the root as its
explicit one. The receipt binds; it does not hide. -/
theorem stage0_statement_carries_word (rc : FsReceipt (Fin 4131 → BabyBear) 4131 13) :
    (rc.output S.commit evmAddDescriptor (bitCorner 13) (by norm_num)).stmt.y = rc.word ∧
      (rc.output S.commit evmAddDescriptor (bitCorner 13) (by norm_num)).stmt.x = rc.root :=
  ⟨rfl, rfl⟩

/-- Stage-0 evidence in the routing model: the public boundary the host claims — operands
`(X, Y)`, released `Z` — and the 4,131-wire word. Neutral data; the gate decides. -/
structure Stage0Evidence where
  X : ℕ
  Y : ℕ
  Z : ℕ
  word : Fin 4131 → BabyBear

/-- The ideal Stage-0 gate — the relation `fsCheck` certifies up to the FS price: in-range
operands, the word's public prefix pinned to the claimed boundary, and the descriptor holding
on the word. Decidable (4,148 residuals — for the executable, not for kernel `decide`). -/
def stage0IdealGate (e : Stage0Evidence) : Bool :=
  decide (e.X < 2 ^ 256) && decide (e.Y < 2 ^ 256) && decide (e.Z < 2 ^ 256) &&
    decide (∀ i : Fin 48, traceOf e.word i.1 = encodeBoundary e.X e.Y e.Z i) &&
    decide (descriptorHolds evmAddDescriptor (traceOf e.word))

/-- The authorized Stage-0 relation: the released `Z` is the wrapped sum of the public
operands; the next state is the operands (a read). -/
def stage0Relation : AuthorizedRelation (ℕ × ℕ) ℕ :=
  fun xy xy' z => xy' = xy ∧ z = (xy.1 + xy.2) % 2 ^ 256

/-- **The descriptor forces the released output**: any total wire vector satisfying
`evmAddDescriptor` whose public prefix reads `(X, Y, Z)` has `Z = (X + Y) mod 2^256` — through
`evmAddDescriptor_means_semantics` (the descriptor ↔ the byte-level EVM run) and
`fragment_run_eq_iff` (the run ↔ the wrapped sum). This is the binding: no assignment of the
4,083 non-public wires routes anything but the designated sum into the output limbs. -/
theorem stage0_released_output_forced (X Y Z : ℕ)
    (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) (hZ : Z < 2 ^ 256)
    (wv : ℕ → BabyBear) (hpin : ∀ i : Fin 48, wv i.1 = encodeBoundary X Y Z i)
    (hd : descriptorHolds evmAddDescriptor wv) : Z = (X + Y) % 2 ^ 256 :=
  (fragment_run_eq_iff X Y Z hX hY hZ).mp
    ((evmAddDescriptor_means_semantics X Y Z hX hY hZ).mp ⟨wv, hpin, hd⟩)

/-- **The Stage-0 ideal gate is a binding gate** for `stage0Relation`. -/
theorem stage0IdealGate_binding :
    BindingGate stage0Relation (fun e => (e.X, e.Y)) Stage0Evidence.Z stage0IdealGate := by
  intro e h
  simp only [stage0IdealGate, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hX, hY⟩, hZ⟩, hpin⟩, hd⟩ := h
  exact ⟨(e.X, e.Y), rfl, stage0_released_output_forced e.X e.Y e.Z hX hY hZ _ hpin hd⟩

theorem stage0Relation_publicOnly :
    PublicOnly stage0Relation id (fun xy => (xy.1 + xy.2) % 2 ^ 256) :=
  fun _ _ _ h => h.2

/-- **Routing refused at Stage 0** (teeth): evidence claiming any `Z` other than the wrapped sum
is refused for EVERY word. The compiled exhibit `Stage0Exhibit.exhibit` runs the same refusal at
the deployed gate on the forged `Z = 4` word for `(1, 2)`. -/
theorem stage0_routing_refused (e : Stage0Evidence) (hne : e.Z ≠ (e.X + e.Y) % 2 ^ 256) :
    stage0IdealGate e = false :=
  routing_refused stage0IdealGate_binding stage0Relation_publicOnly e hne

/-- **Pinned tooth at the exhibit's own forgery**: the claimed `Z = 4` for operands `(1, 2)` is
refused by the ideal gate on EVERY word — in particular on the honest candidate's word with its
output limbs overwritten (`evmAddClaimed 1 2 4`, the compiled exhibit's forged vector). -/
theorem stage0_forged_z_refused (word : Fin 4131 → BabyBear) :
    stage0IdealGate ⟨1, 2, 4, word⟩ = false :=
  stage0_routing_refused ⟨1, 2, 4, word⟩ (by norm_num)

/-- The candidate array has exactly the descriptor's width (`fillAux_size` at the decided shape). -/
theorem evmAddCandidate_size (X Y : ℕ) : (evmAddCandidate X Y).size = 4131 := by
  rw [evmAddCandidate, fillAux_size evmAddDescriptor (Array.ofFn (evmAddAsg X Y))
    evmAddDescriptor_wellFormed Array.size_ofFn, evmAddDescriptor_shape.2.1]

/-- Reading the candidate word as a total trace is reading the candidate array. -/
theorem traceOf_wordOf_candidate (X Y : ℕ) :
    traceOf (wordOf (evmAddCandidate X Y)) = fun i => (evmAddCandidate X Y).getD i 0 := by
  funext i
  by_cases h : i < 4131
  · simp [traceOf, wordOf, h]
  · have hsize : (evmAddCandidate X Y).size ≤ i := by rw [evmAddCandidate_size]; omega
    simp [traceOf, h, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hsize]

/-- **satisfiable / premise-inhabitation** — the honest candidate for in-range operands, with
the claimed `Z` the wrapped sum, is accepted by the ideal gate (`evmAddCandidate_holds` +
`evmAddCandidate_pins`). -/
theorem stage0_honest_accepted (X Y : ℕ) (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) :
    stage0IdealGate ⟨X, Y, (X + Y) % 2 ^ 256, wordOf (evmAddCandidate X Y)⟩ = true := by
  have hpin : ∀ i : Fin 48, traceOf (wordOf (evmAddCandidate X Y)) i.1 =
      encodeBoundary X Y ((X + Y) % 2 ^ 256) i := by
    intro i
    rw [traceOf_wordOf_candidate]
    exact evmAddCandidate_pins X Y i
  have hd : descriptorHolds evmAddDescriptor (traceOf (wordOf (evmAddCandidate X Y))) := by
    rw [traceOf_wordOf_candidate]
    exact evmAddCandidate_holds X Y hX hY
  -- `unfold` + syntactic `rw`: a `show`/`exact` here sends the unifier into lazy delta on
  -- `decide (descriptorHolds …)` and it unfolds the 3,298-gate fill (max recursion).
  unfold stage0IdealGate
  rw [decide_eq_true hX, decide_eq_true hY, decide_eq_true (Nat.mod_lt _ (by norm_num)),
    decide_eq_true hpin, decide_eq_true hd]
  rfl

/-- **satisfiable at the DEPLOYED gate**: the honest candidate's non-interactive receipt at the
cSHAKE oracle is accepted by `fsCheck` (`fsProve_complete` at Stage 0) — so the evidence type
`FsReceipt` is inhabited by an ACCEPTED receipt, not merely by data. -/
theorem stage0_deployed_gate_accepts_honest (X Y : ℕ) (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) :
    ∃ r, fsCheck S.commit evmAddDescriptor (bitCorner 13) (by norm_num) O
      (fsProve S.commit evmAddDescriptor (bitCorner 13) (by norm_num) O
        (S.commit (wordOf (evmAddCandidate X Y))) (wordOf (evmAddCandidate X Y))) = .ok r :=
  ⟨_, fsProve_complete S.commit evmAddDescriptor (bitCorner 13) (by norm_num) O _
    (residualEmbedding evmAddDescriptor _ stage0_residuals_fit)
    (fun _ => rfl)
    (by rw [traceOf_wordOf_candidate]; exact evmAddCandidate_holds X Y hX hY)⟩

/-- **`stage0Receipt_is_bound_evidence`** — the Stage-0 non-interactive receipt as an inhabitant
of the evidence type, in the honest form that types. (a) The deployed controller `fsCheck` at
the cSHAKE oracle accepts only what the tree's `fiatShamir` accepts (`fsCheck_ok_fiatShamir`).
(b) `fiatShamir` accepts a statement OUTSIDE the relation of `stage0_relation_is_descriptor`
with probability at most `(t + 14) · (0 + 4147/p^6 + 13 · 1/p^6)` against any `t`-query
adversary in the lazily-sampled ROM (`stage0Receipt_price`; `p = 2^31 − 2^27 + 1`). So what the
receipt BINDS is the descriptor on the word (hence, by `stage0_released_output_forced`, the
released `Z` to the public `(X, Y)`) — up to that price, under the ROM. What it does NOT do:
hide (`[RELEASE-hiding]`, `stage0_statement_carries_word`), or certify currency
(`[RELEASE-continuity]`). The cSHAKE realizing the ROM is `[FS-ROM]`. -/
theorem stage0Receipt_is_bound_evidence :
    (∀ (rc : FsReceipt (Fin 4131 → BabyBear) 4131 13)
        (r : CommittedTerminalController.Receipt (Fin 4131 → BabyBear) 13),
      fsCheck S.commit evmAddDescriptor (bitCorner 13) (by norm_num) O rc = .ok r →
        fiatShamir stage0Reduction 0 O
            (rc.output S.commit evmAddDescriptor (bitCorner 13) (by norm_num)) =
          some ((), fun _ => ())) ∧
    FsStraightlineKnowledgeSoundness stage0Reduction Set.univ
      (fun _s t _δ => ((t : ℝ) + (13 + 1 : ℝ)) *
        ((0 : ℝ) + ((4148 - 1 : ℕ) : ℝ) / ((2013265921 : ℝ) ^ 6) +
          (13 : ℝ) * (1 / ((2013265921 : ℝ) ^ 6)))) :=
  ⟨fun rc r h => fsCheck_ok_fiatShamir S.commit evmAddDescriptor (bitCorner 13) (by norm_num) O rc r h,
    Stage0.stage0Receipt_price S⟩

end Stage0

/-! ## §4. Axiom pins -/

/-- info: 'Minidregg.Assurance.ReleaseGateRouting.determines_iff_separates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms determines_iff_separates
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.routing_of_projections' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms routing_of_projections
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.single_predicate_not_determining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms single_predicate_not_determining
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.single_gate_two_states_one_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms single_gate_two_states_one_bit
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.routing_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms routing_refused
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.binding_release_public_only' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms binding_release_public_only
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.TwoBit.routed_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms TwoBit.routed_refused
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.TwoBit.private_bit_not_released' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms TwoBit.private_bit_not_released
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.acceptable_pins_named_relation' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms acceptable_pins_named_relation
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.settlement_release_public_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms settlement_release_public_only
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.stage0_relation_is_descriptor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stage0_relation_is_descriptor
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.stage0_released_output_forced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stage0_released_output_forced
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.stage0IdealGate_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stage0IdealGate_binding
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.stage0_routing_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stage0_routing_refused
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.stage0_forged_z_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stage0_forged_z_refused
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.stage0_honest_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stage0_honest_accepted
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.stage0_deployed_gate_accepts_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stage0_deployed_gate_accepts_honest
/-- info: 'Minidregg.Assurance.ReleaseGateRouting.stage0Receipt_is_bound_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stage0Receipt_is_bound_evidence

end Minidregg.Assurance.ReleaseGateRouting
