/-
# `Compiler/AdmissionAir.lean` — [ADMISSION-air]: gated admission (Verb = admission × footprint), DERIVED through the DSL

The kernel's turn is fired through a GATE: a verb acts only when (a) the actor holds a
CAPABILITY that authorizes it and (b) the action stays inside its declared FOOTPRINT.
This file arithmetizes that gate — the generic admission SHAPE — as a `ConstraintSystem`
grown from the landed gadgets. The gated executor comes OUT OF THE COMPILER; no
executor arm, no constraint, no `air_accepts` is hand-written — the [N-TURN] tripwire
(AIR authored in Lean, derived path only) closed the RIGHT way.

**Substrate, said out loud: this is Lean-authored arithmetization.** Every constraint
below is a `Term (AirSig F Idx)` built from the DSL surface (`vr`/`cst`/`add'`/`mul'`)
or produced by the landed gadgets — `hashConstraint` (`AirHash`), `membershipGadget`
(`AirMembership`), `boolGadget` (rung 1) — REUSED, never re-derived, all read through
the one fold (`eval = fold evalAlg`); composition is `List.append` on
`ConstraintSystem`s and its meaning is rung 1's initiality keystone lifted pointwise
(`systemAccepts_iff_systemSemHolds`). NO Rust, no bespoke executor.

## The construction (the two gate legs, and the coupling that makes them one gate)

The wire layout of one admission instance (`ι = 1` slice — ONE capability admitting a
turn over an `n`-cell witnessed window):

* ADMISSION (the capability leg): the turn carries a capability witness — `w` field
  wires `capW` (`capW tIdx` its TARGET cell id) — and the leg asserts the capability is
  IN the authority set: `capW` hashes to the commitment wire `capHashW`
  (`hashConstraint`, reused) and `capHashW` is a Merkle member of the authority tree at
  the public root `rootW` (`membershipGadget`, reused). Holding-a-capability is
  set-membership under a committed authority table.
* FOOTPRINT (the frame leg): per witnessed cell `i`, a declared-footprint flag `fpW i`,
  a cell id `cellW i`, and pre/post state wires `preW i`/`postW i`. Constraints:
  `boolGadget (fpW i)` (the flag vector decodes to a SET), and the FRAME term
  `(1 − fpᵢ)·(postᵢ − preᵢ) ≐ 0` — an undeclared cell provably stands still;
  contrapositively every TOUCHED cell (postᵢ ≠ preᵢ) is forced into the declared
  footprint. "Touched ⊆ declared" and "non-footprint unchanged" are the two readings
  of the one constraint.
* THE COUPLING (what makes it a gate, not a bare product): the TARGET term
  `fpᵢ·(cellᵢ − capW tIdx) ≐ 0` — every DECLARED cell is the capability's target. A
  capability for cell 3 cannot admit a turn declaring cell 9: authorization is OF THE
  CELLS TOUCHED, not mere possession.

An `ι = N` joint turn (the hyperedge) is `N` of these systems appended, one per
incidence — same composition discipline as `NoteSpend`.

## Statement-first (the ATLAS fields)

* `AdmissionHolds` (stated FIRST, §1) = `CapAuthorizes` (cap hashes into the authority
  set at the root) ∧ `FootprintRespected` (flags boolean + frame) ∧ `TargetCovers`
  (declared cells are the capability's target).
* `admission_correct` — the keystone iff: the system accepts `asg` **iff**
  `AdmissionHolds` at the assignment's values. Derived from `systemAccepts_append` +
  the landed gadgets' `_correct` iffs — no new induction, no bespoke soundness.
* `admission_authorizes` — soundness, ∃-form: any accepted assignment's capability IS a
  `memberAtDepth` member of the authority tree (via `memberAtDepth_of_muxFold`, reused).
* `admission_gates_touch` — the footprint tooth, general form: an accepted turn that
  CHANGES cell `i` has `fpᵢ = 1` (touched ⊆ declared, forced).
* `admission_covers` — the coupling, general form: an accepted turn's declared cells
  all carry the capability's target id.
* `admission_complete` — premise-inhabitation: every genuinely authorized,
  footprint-respecting turn has its accepting assignment (the canonical `admAsg`).
* Keystones BUILT (ZMod 7: footprint leg; ZMod 13: the full gate on `demoSpec`):
  satisfiable — an authorized turn with a valid capability and respected footprint
  ACCEPTS, computed; teeth with machine-checked attribution — a rights-escalation
  forgery (same target, tampered rights word) is rejected BOTH ways (honest hash ⇒
  membership rejects; forged hash wire ⇒ the hash constraint rejects), a fully
  AUTHORIZED turn touching an undeclared cell is rejected (the frame's doing — the
  culprit named), a declared cell outside the capability's target is rejected (the
  coupling's doing), a non-boolean flag is rejected (booleanity's doing), and the
  capability-hash wire is FORCED (quantified over the field).

## The kernel correspondence (PROSE — `Compiler` does not import `Kernel`)

This gadget arithmetizes the Verb-admission of the kernel's turn:

* `Kernel/Turn.lean`'s `Hyperedge` is THE turn — a wide pullback of incidences firing
  one shared turn. What a turn is ALLOWED to do at each incidence is the gate this
  file derives: admission × footprint.
* `Kernel/State.lean`'s `caps : CellId → List Cap` is the authority plane, and `Cap`
  is `{target, rights}`. ADMISSION here = "the witness capability is in the committed
  authority set" — the deployed realization of `cap ∈ k.caps holder` once the slot
  table is committed as a Merkle set; the TARGET coupling is `Cap.target` covering the
  touched cells (the `ι = 1` slice).
* FOOTPRINT here = the frame discipline the kernel's verbs obey as theorems
  (`move` touches only the `bal` column — `Kernel/State`; `create`/`gwrite` carry
  their own frame theorems — `Kernel/Verbs`): undeclared cells provably unchanged,
  arithmetized over the witnessed window.

The emitted AIR (through `Compiler/Emit`, which consumes any `ConstraintSystem`) is
therefore the kernel's GATED EXECUTOR, derived — the gate exists as a constraint
system produced by the compiler, never as a hand-authored executor arm.

**`[ADMISSION-kernel-bridge]`** — the NAMED follow-on (Assurance-side, where both
`Kernel` and `Compiler` are importable): prove this gadget's `AdmissionHolds` IS the
kernel's actual admission predicate — (a) `CapAuthorizes` at a root that commits
`k.caps` ⟺ `cap ∈ k.caps holder`, (b) the `rights` word decoded and checked against
the fired verb (the rights-decode gadget is vocabulary this rung already carries:
bit-decompose `capW rightsIdx` with `rangeGadget` and gate per-verb bits), (c) the
window frame extended to the GLOBAL frame — cells outside the witnessed window stand
still because the state ROOT only reopens footprint cells (the state-commitment
discipline), and (d) cross-incidence footprint DISJOINTNESS for `ι = N` turns
(`Σᵢ fp¹ᵢ·fp²ᵢ ≐ 0` — expressible in this DSL today). Until that bridge lands, the
claim on this file's label is exactly `admission_correct` and nothing more.
-/
import Compiler.NoteSpend

namespace Minidregg.Compiler

universe u

variable {F : Type u} [Field F] {Idx : Type u} {w n : ℕ}

/-! ## §1. The admission statement — STATED FIRST, before any gadget.

Value-level `Prop`s over field values (no wires): what an accepting assignment MUST
mean. The gadgets of §2–§3 are then proved to impose exactly these. -/

/-- **The capability authorizes**: the capability witness `cap` hashes to `capHash`
(`capSpec`), and `capHash` sits in the authority tree at `root` along the (mux-encoded)
path values `pvals` with boolean direction values. On boolean directions the fold IS
the reference `merkleExec` (`merkleMuxExec_encode`), so this reads: the capability is a
MEMBER of the committed authority set. (That forging membership needs a hash collision
is `[COMMIT-CR]`, the named floor — inherited, never claimed here.) -/
def CapAuthorizes [NeZero w] (capSpec : PermSpec F w) (trSpec : PermSpec F 2)
    (root capHash : F) (cap : Fin w → F) (pvals : List (F × F)) : Prop :=
  capHash = hashExec capSpec cap ∧
    ((∀ sd ∈ pvals, sd.2 = 0 ∨ sd.2 = 1) ∧ root = merkleMuxExec trSpec capHash pvals)

/-- **The footprint is respected**: the declared-footprint flags are boolean (the flag
vector decodes to a SET — the declared footprint as data), and every UNDECLARED cell
stands still (the frame). Contrapositively — `footprint_gates_touch` below — every
touched cell is declared. -/
def FootprintRespected {n : ℕ} (fp pre post : Fin n → F) : Prop :=
  (∀ i, fp i = 0 ∨ fp i = 1) ∧ ∀ i, fp i = 0 → post i = pre i

/-- **The target covers the declared cells**: every witnessed cell is either undeclared
or carries the capability's target id — authorization is OF the cells touched. (The
`∨`-form is the raw term meaning; under booleanity it reads `fp i = 1 → cell i =
target`, `admission_covers` below.) -/
def TargetCovers {n : ℕ} (target : F) (fp cellId : Fin n → F) : Prop :=
  ∀ i, fp i = 0 ∨ cellId i = target

/-- **THE ADMISSION STATEMENT** — Verb = admission × footprint, coupled: the capability
is in the authority set, the footprint is respected, and the declared cells are the
capability's target (`cap tIdx` the target field). -/
def AdmissionHolds [NeZero w] (capSpec : PermSpec F w) (trSpec : PermSpec F 2)
    (tIdx : Fin w) (root capHash : F) (cap : Fin w → F) (pvals : List (F × F))
    {n : ℕ} (fp cellId pre post : Fin n → F) : Prop :=
  CapAuthorizes capSpec trSpec root capHash cap pvals ∧
    (FootprintRespected fp pre post ∧ TargetCovers (cap tIdx) fp cellId)

instance {n : ℕ} [DecidableEq F] (fp pre post : Fin n → F) :
    Decidable (FootprintRespected fp pre post) :=
  inferInstanceAs (Decidable ((∀ i, fp i = 0 ∨ fp i = 1) ∧ ∀ i, fp i = 0 → post i = pre i))

instance {n : ℕ} [DecidableEq F] (target : F) (fp cellId : Fin n → F) :
    Decidable (TargetCovers target fp cellId) :=
  inferInstanceAs (Decidable (∀ i, fp i = 0 ∨ cellId i = target))

instance [NeZero w] [DecidableEq F] (capSpec : PermSpec F w) (trSpec : PermSpec F 2)
    (root capHash : F) (cap : Fin w → F) (pvals : List (F × F)) :
    Decidable (CapAuthorizes capSpec trSpec root capHash cap pvals) :=
  inferInstanceAs (Decidable (capHash = hashExec capSpec cap ∧
    ((∀ sd ∈ pvals, sd.2 = 0 ∨ sd.2 = 1) ∧ root = merkleMuxExec trSpec capHash pvals)))

instance [NeZero w] [DecidableEq F] (capSpec : PermSpec F w) (trSpec : PermSpec F 2)
    (tIdx : Fin w) (root capHash : F) (cap : Fin w → F) (pvals : List (F × F))
    {n : ℕ} (fp cellId pre post : Fin n → F) :
    Decidable (AdmissionHolds capSpec trSpec tIdx root capHash cap pvals fp cellId pre post) :=
  inferInstanceAs (Decidable (CapAuthorizes capSpec trSpec root capHash cap pvals ∧
    (FootprintRespected fp pre post ∧ TargetCovers (cap tIdx) fp cellId)))

/-! ## §2. The two new terms — frame and target coupling, DSL surface only. -/

/-- The FRAME term: `(1 + (−1)·f)·(post + (−1)·pre)`, i.e. `(1 − f)·(post − pre) ≐ 0`
— at `f = 0` the cell must stand still; at `f = 1` it is free. -/
def frameTerm (f pre post : Idx) : Term (AirSig F Idx) :=
  mul' (add' (cst 1) (mul' (cst (-1)) (vr f)))
    (add' (vr post) (mul' (cst (-1)) (vr pre)))

/-- The frame term MEANS the frame: it accepts iff the flag is `1` or the cell is
unchanged. -/
theorem frameTerm_correct (asg : Idx → F) (f pre post : Idx) :
    accepts asg (frameTerm f pre post) ↔ (asg f = 1 ∨ asg post = asg pre) := by
  unfold accepts frameTerm
  simp only [eval_mul', eval_add', eval_cst, eval_vr]
  rw [neg_one_mul, neg_one_mul, ← sub_eq_add_neg, ← sub_eq_add_neg, mul_eq_zero,
    sub_eq_zero, sub_eq_zero]
  exact or_congr eq_comm Iff.rfl

/-- The TARGET term: `f·(cell + (−1)·target)`, i.e. `f·(cell − target) ≐ 0` — a
DECLARED cell (`f = 1`) must carry the capability's target id. -/
def targetTerm (f cellId target : Idx) : Term (AirSig F Idx) :=
  mul' (vr f) (add' (vr cellId) (mul' (cst (-1)) (vr target)))

/-- The target term MEANS the coupling: it accepts iff the flag is `0` or the cell id
is the target. -/
theorem targetTerm_correct (asg : Idx → F) (f cellId target : Idx) :
    accepts asg (targetTerm f cellId target) ↔ (asg f = 0 ∨ asg cellId = asg target) := by
  unfold accepts targetTerm
  simp only [eval_mul', eval_add', eval_cst, eval_vr]
  rw [neg_one_mul, ← sub_eq_add_neg, mul_eq_zero, sub_eq_zero]

/-! ## §3. The three sub-gadgets and their iffs. -/

/-- **The footprint gadget**: one booleanity assertion (rung 1's `boolGadget`, reused)
plus one frame term per witnessed cell. -/
def footprintGadget (fpW preW postW : Fin n → Idx) : ConstraintSystem F Idx :=
  ((List.finRange n).map fun i => boolGadget (fpW i)) ++
    ((List.finRange n).map fun i => frameTerm (fpW i) (preW i) (postW i))

/-- The footprint gadget means `FootprintRespected` — booleanity per flag +
`frameTerm_correct` per cell, the `0 ≠ 1` of the field converting the term's `∨`-form
into the frame implication. -/
theorem footprint_correct (asg : Idx → F) (fpW preW postW : Fin n → Idx) :
    systemAccepts asg (footprintGadget fpW preW postW) ↔
      FootprintRespected (fun i => asg (fpW i)) (fun i => asg (preW i))
        (fun i => asg (postW i)) := by
  unfold systemAccepts footprintGadget FootprintRespected
  constructor
  · intro h
    have hbool : ∀ i, asg (fpW i) = 0 ∨ asg (fpW i) = 1 := fun i =>
      (boolGadget_correct asg (fpW i)).mp
        (h _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)))
    refine ⟨hbool, fun i h0 => ?_⟩
    rcases (frameTerm_correct asg (fpW i) (preW i) (postW i)).mp
        (h _ (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)))
      with h1 | heq
    · exact absurd (h0.symm.trans h1) zero_ne_one
    · exact heq
  · rintro ⟨hbool, hframe⟩ t ht
    rcases List.mem_append.mp ht with ht' | ht'
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht'
      exact (boolGadget_correct asg (fpW i)).mpr (hbool i)
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht'
      refine (frameTerm_correct asg (fpW i) (preW i) (postW i)).mpr ?_
      rcases hbool i with h0 | h1
      · exact Or.inr (hframe i h0)
      · exact Or.inl h1

/-- **Touched ⊆ declared, general form**: an accepted assignment that CHANGES cell `i`
has its flag forced to `1` — the footprint genuinely gates what may move. -/
theorem footprint_gates_touch (asg : Idx → F) (fpW preW postW : Fin n → Idx)
    (hacc : systemAccepts asg (footprintGadget fpW preW postW)) (i : Fin n)
    (hne : asg (postW i) ≠ asg (preW i)) : asg (fpW i) = 1 := by
  obtain ⟨hbool, hframe⟩ := (footprint_correct asg fpW preW postW).mp hacc
  rcases hbool i with h0 | h1
  · exact absurd (hframe i h0) hne
  · exact h1

/-- **The target gadget**: one coupling term per witnessed cell. -/
def targetGadget (targetW : Idx) (fpW cellW : Fin n → Idx) : ConstraintSystem F Idx :=
  (List.finRange n).map fun i => targetTerm (fpW i) (cellW i) targetW

/-- The target gadget means `TargetCovers`. -/
theorem target_correct (asg : Idx → F) (targetW : Idx) (fpW cellW : Fin n → Idx) :
    systemAccepts asg (targetGadget targetW fpW cellW) ↔
      TargetCovers (asg targetW) (fun i => asg (fpW i)) (fun i => asg (cellW i)) := by
  unfold systemAccepts targetGadget TargetCovers
  constructor
  · intro h i
    exact (targetTerm_correct asg (fpW i) (cellW i) targetW).mp
      (h _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
  · intro h t ht
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
    exact (targetTerm_correct asg (fpW i) (cellW i) targetW).mpr (h i)

/-- **The capability gadget**: the witness hashes to the commitment wire
(`hashConstraint`, reused) and the commitment is a member of the authority tree
(`membershipGadget`, reused). -/
def capabilityGadget [NeZero w] (capSpec : PermSpec F w) (trSpec : PermSpec F 2)
    (capW : Fin w → Idx) (capHashW rootW : Idx) (capPath : List (Idx × Idx)) :
    ConstraintSystem F Idx :=
  hashConstraint capSpec capHashW capW ++
    membershipGadget trSpec capHashW rootW capPath

/-- The capability gadget means `CapAuthorizes`. -/
theorem capability_correct [NeZero w] (asg : Idx → F) (capSpec : PermSpec F w)
    (trSpec : PermSpec F 2) (capW : Fin w → Idx) (capHashW rootW : Idx)
    (capPath : List (Idx × Idx)) :
    systemAccepts asg (capabilityGadget capSpec trSpec capW capHashW rootW capPath) ↔
      CapAuthorizes capSpec trSpec (asg rootW) (asg capHashW) (fun i => asg (capW i))
        (capPath.map fun sd => (asg sd.1, asg sd.2)) := by
  unfold capabilityGadget CapAuthorizes
  rw [systemAccepts_append, hashConstraint_correct, membership_correct]
  simp only [List.forall_mem_map]

/-! ## §4. THE ADMISSION GADGET and its keystone iff. -/

/-- **The gated-admission system** `[ADMISSION-air]`: capability (hash + authority
membership) ++ footprint (booleanity + frame) ++ target coupling — all landed gadgets
and DSL terms, composed by list append, over ONE shared assignment. The `ι = 1` slice
of the hyperedge's gate; `ι = N` is `N` of these appended. -/
def admissionGadget [NeZero w] (capSpec : PermSpec F w) (trSpec : PermSpec F 2)
    (capW : Fin w → Idx) (tIdx : Fin w) (capHashW rootW : Idx)
    (capPath : List (Idx × Idx)) (fpW cellW preW postW : Fin n → Idx) :
    ConstraintSystem F Idx :=
  capabilityGadget capSpec trSpec capW capHashW rootW capPath ++
    (footprintGadget fpW preW postW ++ targetGadget (capW tIdx) fpW cellW)

/-- **`admission_correct` — the keystone iff.** The system accepts `asg` IFF
`AdmissionHolds` at the assignment's values: the capability hashes into the authority
set at the root, the footprint flags are boolean with undeclared cells framed still,
and declared cells carry the capability's target. Derived from `systemAccepts_append`
+ `capability_correct` + `footprint_correct` + `target_correct` — no new induction,
no bespoke soundness argument. -/
theorem admission_correct [NeZero w] (asg : Idx → F) (capSpec : PermSpec F w)
    (trSpec : PermSpec F 2) (capW : Fin w → Idx) (tIdx : Fin w) (capHashW rootW : Idx)
    (capPath : List (Idx × Idx)) (fpW cellW preW postW : Fin n → Idx) :
    systemAccepts asg
        (admissionGadget capSpec trSpec capW tIdx capHashW rootW capPath
          fpW cellW preW postW) ↔
      AdmissionHolds capSpec trSpec tIdx (asg rootW) (asg capHashW)
        (fun i => asg (capW i)) (capPath.map fun sd => (asg sd.1, asg sd.2))
        (fun i => asg (fpW i)) (fun i => asg (cellW i))
        (fun i => asg (preW i)) (fun i => asg (postW i)) := by
  unfold admissionGadget AdmissionHolds
  rw [systemAccepts_append, systemAccepts_append, capability_correct, footprint_correct,
    target_correct]

/-- The EXECUTOR reading of the keystone, via rung 1's initiality transfer — drift
between the circuit and executor readings stays impossible at the gate level. -/
theorem admission_semHolds_correct [NeZero w] (asg : Idx → F) (capSpec : PermSpec F w)
    (trSpec : PermSpec F 2) (capW : Fin w → Idx) (tIdx : Fin w) (capHashW rootW : Idx)
    (capPath : List (Idx × Idx)) (fpW cellW preW postW : Fin n → Idx) :
    systemSemHolds asg
        (admissionGadget capSpec trSpec capW tIdx capHashW rootW capPath
          fpW cellW preW postW) ↔
      AdmissionHolds capSpec trSpec tIdx (asg rootW) (asg capHashW)
        (fun i => asg (capW i)) (capPath.map fun sd => (asg sd.1, asg sd.2))
        (fun i => asg (fpW i)) (fun i => asg (cellW i))
        (fun i => asg (preW i)) (fun i => asg (postW i)) := by
  rw [← systemAccepts_iff_systemSemHolds, admission_correct]

/-- **`admission_authorizes` — soundness, ∃-form.** Any accepted assignment's
capability IS a member of the authority tree at the exposed root: the boolean path
values decode to a genuine `Bool` path (`memberAtDepth_of_muxFold`, reused from
`NoteSpend`). What no theorem here claims: that membership cannot be FORGED — that is
`[COMMIT-CR]`, collision resistance of the instantiated hash, the named floor. -/
theorem admission_authorizes [NeZero w] (asg : Idx → F) (capSpec : PermSpec F w)
    (trSpec : PermSpec F 2) (capW : Fin w → Idx) (tIdx : Fin w) (capHashW rootW : Idx)
    (capPath : List (Idx × Idx)) (fpW cellW preW postW : Fin n → Idx)
    (hacc : systemAccepts asg
      (admissionGadget capSpec trSpec capW tIdx capHashW rootW capPath
        fpW cellW preW postW)) :
    memberAtDepth trSpec capPath.length (asg rootW)
      (hashExec capSpec fun i => asg (capW i)) := by
  rw [admission_correct] at hacc
  obtain ⟨⟨hhash, hbits, hroot⟩, -⟩ := hacc
  have h := memberAtDepth_of_muxFold trSpec (asg capHashW) (asg rootW) _ hbits hroot
  rw [List.length_map] at h
  rwa [hhash] at h

/-- **The footprint tooth through the full gate**: an accepted admission that CHANGES
cell `i` has declared it — touched ⊆ declared, forced by the frame + booleanity. -/
theorem admission_gates_touch [NeZero w] (asg : Idx → F) (capSpec : PermSpec F w)
    (trSpec : PermSpec F 2) (capW : Fin w → Idx) (tIdx : Fin w) (capHashW rootW : Idx)
    (capPath : List (Idx × Idx)) (fpW cellW preW postW : Fin n → Idx)
    (hacc : systemAccepts asg
      (admissionGadget capSpec trSpec capW tIdx capHashW rootW capPath
        fpW cellW preW postW))
    (i : Fin n) (hne : asg (postW i) ≠ asg (preW i)) : asg (fpW i) = 1 := by
  rw [admission_correct] at hacc
  obtain ⟨-, ⟨hbool, hframe⟩, -⟩ := hacc
  rcases hbool i with h0 | h1
  · exact absurd (hframe i h0) hne
  · exact h1

/-- **The coupling tooth through the full gate**: an accepted admission's DECLARED
cells all carry the capability's target id — authorization is of the cells touched. -/
theorem admission_covers [NeZero w] (asg : Idx → F) (capSpec : PermSpec F w)
    (trSpec : PermSpec F 2) (capW : Fin w → Idx) (tIdx : Fin w) (capHashW rootW : Idx)
    (capPath : List (Idx × Idx)) (fpW cellW preW postW : Fin n → Idx)
    (hacc : systemAccepts asg
      (admissionGadget capSpec trSpec capW tIdx capHashW rootW capPath
        fpW cellW preW postW))
    (i : Fin n) (hdecl : asg (fpW i) = 1) : asg (cellW i) = asg (capW tIdx) := by
  rw [admission_correct] at hacc
  obtain ⟨-, -, htc⟩ := hacc
  rcases htc i with h0 | hc
  · exact absurd (h0.symm.trans hdecl) zero_ne_one
  · exact hc

/-! ## §5. The canonical wire layout and completeness. -/

/-- Canonical wire layout for a `w`-field capability, `n`-cell window, depth-`depth`
authority tree. -/
inductive AWire (w n depth : ℕ) : Type u where
  | capW (i : Fin w)
  | capHashW
  | rootW
  | sibW (j : Fin depth)
  | dirW (j : Fin depth)
  | fpW (i : Fin n)
  | cellW (i : Fin n)
  | preW (i : Fin n)
  | postW (i : Fin n)

/-- The canonical `(sibling, direction)` wire list. -/
def admPath (w n depth : ℕ) : List (AWire.{u} w n depth × AWire.{u} w n depth) :=
  List.ofFn fun j => (AWire.sibW j, AWire.dirW j)

theorem admPath_length (w n depth : ℕ) : (admPath.{u} w n depth).length = depth := by
  simp [admPath]

/-- The canonical accepting assignment: the capability on its wires, its hash on the
commitment wire, the `Bool` authority path encoded onto sibling/direction wires, and
the window data on the footprint/cell/pre/post wires. -/
def admAsg (cap : Fin w → F) (ch root : F) (bpath : List (F × Bool))
    (fp cellId pre post : Fin n → F) : AWire.{u} w n bpath.length → F
  | .capW i => cap i
  | .capHashW => ch
  | .rootW => root
  | .sibW j => (bpath.get j).1
  | .dirW j => encodeBit (bpath.get j).2
  | .fpW i => fp i
  | .cellW i => cellId i
  | .preW i => pre i
  | .postW i => post i

/-- Reading the canonical assignment along the canonical wires recovers the encoded
path. -/
theorem admAsg_map (cap : Fin w → F) (ch root : F) (bpath : List (F × Bool))
    (fp cellId pre post : Fin n → F) :
    ((admPath w n bpath.length).map fun sd =>
        (admAsg cap ch root bpath fp cellId pre post sd.1,
          admAsg cap ch root bpath fp cellId pre post sd.2))
      = bpath.map encodeStep := by
  show List.map _ (List.ofFn _) = _
  rw [List.map_ofFn]
  show List.ofFn (encodeStep ∘ bpath.get) = _
  rw [← List.map_ofFn, List.ofFn_get]

/-- Encoded direction values are boolean — the mpr-side bridge. -/
theorem encoded_bits (bpath : List (F × Bool)) :
    ∀ sd ∈ bpath.map (encodeStep (F := F)), sd.2 = 0 ∨ sd.2 = 1 := by
  intro sd hsd
  obtain ⟨⟨s, b⟩, -, rfl⟩ := List.mem_map.mp hsd
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Completeness / premise-inhabitation**: every genuinely authorized turn — a
capability whose hash folds up a real `Bool` path to the authority root — with a
respected footprint and covered targets HAS its accepting assignment, the canonical
one. The iff of `admission_correct` has teeth in both directions. -/
theorem admission_complete [NeZero w] (capSpec : PermSpec F w) (trSpec : PermSpec F 2)
    (tIdx : Fin w) (cap : Fin w → F) (root : F) (bpath : List (F × Bool))
    (fp cellId pre post : Fin n → F)
    (hroot : merkleExec trSpec (hashExec capSpec cap) bpath = root)
    (hfp : ∀ i, fp i = 0 ∨ fp i = 1)
    (hframe : ∀ i, fp i = 0 → post i = pre i)
    (htarget : ∀ i, fp i = 0 ∨ cellId i = cap tIdx) :
    systemAccepts (admAsg cap (hashExec capSpec cap) root bpath fp cellId pre post)
      (admissionGadget capSpec trSpec AWire.capW tIdx AWire.capHashW AWire.rootW
        (admPath w n bpath.length) AWire.fpW AWire.cellW AWire.preW AWire.postW) := by
  rw [admission_correct]
  refine ⟨⟨rfl, ?_, ?_⟩, ⟨hfp, hframe⟩, htarget⟩
  · rw [admAsg_map]
    exact encoded_bits bpath
  · rw [admAsg_map, merkleMuxExec_encode]
    exact hroot.symm

/-! ## §6. Keystone witnesses — BUILT, both legs load-bearing, attribution
machine-checked.

**ZMod 7 — the footprint leg standalone** (`n = 2`; cell 0 undeclared, cell 1
declared). -/

/-- Footprint-leg wire layout for the ZMod 7 keystones. -/
inductive FWire (n : ℕ) : Type where
  | fpW (i : Fin n)
  | preW (i : Fin n)
  | postW (i : Fin n)

/-- Keystone assignment on the footprint wires. -/
def fpAsg (fp pre post : Fin 2 → ZMod 7) : FWire 2 → ZMod 7
  | .fpW i => fp i
  | .preW i => pre i
  | .postW i => post i

/-- *Satisfiable, computed raw*: flags `(0,1)`, pre `(3,5)`, post `(3,2)` — the
declared cell moves, the undeclared cell stands still — ACCEPTS. -/
example : systemAccepts (fpAsg ![0, 1] ![3, 5] ![3, 2])
    (footprintGadget FWire.fpW FWire.preW FWire.postW) := by decide

/-- *Teeth (frame), computed*: the UNDECLARED cell 0 changes (`3 → 4`) — REJECTED.
Touching outside the declared footprint is what the gate forbids. -/
example : ¬ systemAccepts (fpAsg ![0, 1] ![3, 5] ![4, 2])
    (footprintGadget FWire.fpW FWire.preW FWire.postW) := by decide

/-- *…attribution, machine-checked*: booleanity and the declared cell's frame all
accept that assignment; cell 0's frame term ALONE rejects — the frame did it. -/
example : (∀ i : Fin 2, accepts (fpAsg ![0, 1] ![3, 5] ![4, 2]) (boolGadget (FWire.fpW i))) ∧
    accepts (fpAsg ![0, 1] ![3, 5] ![4, 2])
      (frameTerm (FWire.fpW 1) (FWire.preW 1) (FWire.postW 1)) ∧
    ¬ accepts (fpAsg ![0, 1] ![3, 5] ![4, 2])
      (frameTerm (FWire.fpW 0) (FWire.preW 0) (FWire.postW 0)) := by decide

/-- *Teeth (booleanity), computed*: flag `3 ∉ {0,1}` is REJECTED even with every cell
standing still — the flag vector must decode to a genuine SET. -/
example : ¬ systemAccepts (fpAsg ![3, 1] ![3, 5] ![3, 2])
    (footprintGadget FWire.fpW FWire.preW FWire.postW) := by decide

/-- *…attribution*: both frame terms accept (`(1−3)·0 = 0`); `boolGadget` on flag 0
ALONE rejects — booleanity did it. -/
example : (∀ i : Fin 2, accepts (fpAsg ![3, 1] ![3, 5] ![3, 2])
      (frameTerm (FWire.fpW i) (FWire.preW i) (FWire.postW i))) ∧
    ¬ accepts (fpAsg ![3, 1] ![3, 5] ![3, 2]) (boolGadget (FWire.fpW 0)) := by decide

/-- *The touched cell's flag is FORCED, quantified over the whole field*: every flag
value under which the changed cell 0 is accepted equals `1` — `footprint_gates_touch`
exhibited by exhaustion. -/
example : ∀ f : ZMod 7, systemAccepts (fpAsg ![f, 1] ![3, 5] ![4, 2])
    (footprintGadget FWire.fpW FWire.preW FWire.postW) → f = 1 := by decide

/-! **ZMod 13 — the full gate** on `AirHash`'s `demoSpec` (capability hash AND tree
compression), `w = 2` (capability = target id, rights word — `tIdx = 0`), `n = 2`,
depth 2.

The authority set: capability `(3, 8)` — target cell 3, rights word 8 — hashes to `7`
(`H(3,8) = 7`), a member of the authority tree at root `11` via siblings `(4, 7)`,
directions `(1, 0)` (the `AirMembership` demo tree). The witnessed window: cell ids
`(9, 3)`, flags `(0, 1)` — cell 3 declared (the capability's target), cell 9 not —
pre `(5, 5)`, post `(5, 2)`.

The forgery: capability `(3, 9)` — SAME target, TAMPERED rights word (a
rights-escalation attempt). `H(3,9) = 6 ≠ 7`, and `6` folds up the same path to
`4 ≠ 11`: not in the authority set. -/

/-- Keystone assignment on the canonical wires (`w = 2`, `n = 2`, depth 2). -/
def admKeyAsg (cap : Fin 2 → ZMod 13) (ch root : ZMod 13) (sib dir : Fin 2 → ZMod 13)
    (fp cellId pre post : Fin 2 → ZMod 13) : AWire 2 2 2 → ZMod 13
  | .capW i => cap i
  | .capHashW => ch
  | .rootW => root
  | .sibW j => sib j
  | .dirW j => dir j
  | .fpW i => fp i
  | .cellW i => cellId i
  | .preW i => pre i
  | .postW i => post i

/-- The demo admission system — the full gate at the demo parameters. -/
abbrev demoAdmission : ConstraintSystem (ZMod 13) (AWire 2 2 2) :=
  admissionGadget demoSpec demoSpec AWire.capW 0 AWire.capHashW AWire.rootW
    (admPath 2 2 2) AWire.fpW AWire.cellW AWire.preW AWire.postW

/-- *The demo values are computed, not asserted*: the authorized capability's hash and
root, and the forged capability's (differing) hash and root. -/
example : hashExec demoSpec ![3, 8] = (7 : ZMod 13) ∧
    merkleExec demoSpec 7 [(4, true), (7, false)] = (11 : ZMod 13) ∧
    hashExec demoSpec ![3, 9] = (6 : ZMod 13) ∧
    merkleExec demoSpec 6 [(4, true), (7, false)] = (4 : ZMod 13) := by decide

/-- *SATISFIABLE — an authorized turn ACCEPTS, computed*: valid capability `(3, 8)`
(hash `7`, member at root `11`), declared footprint = its target cell `3`, undeclared
cell `9` untouched. The gate opens for exactly this. -/
example : systemAccepts
    (admKeyAsg ![3, 8] 7 11 ![4, 7] ![1, 0] ![0, 1] ![9, 3] ![5, 5] ![5, 2])
    demoAdmission := by
  rw [admission_correct]
  decide

/-- *TEETH (unauthorized — rights escalation, honest hash)*: capability `(3, 9)` —
same target, tampered rights — with its HONEST hash `6` under the authority root `11`
is REJECTED: `6` is not in the authority set. -/
example : ¬ systemAccepts
    (admKeyAsg ![3, 9] 6 11 ![4, 7] ![1, 0] ![0, 1] ![9, 3] ![5, 5] ![5, 2])
    demoAdmission := by
  rw [admission_correct]
  decide

/-- *…attribution*: hash constraint, footprint, and target coupling all accept that
forgery — the authority MEMBERSHIP alone rejects it. -/
example : systemAccepts
    (admKeyAsg ![3, 9] 6 11 ![4, 7] ![1, 0] ![0, 1] ![9, 3] ![5, 5] ![5, 2])
    (hashConstraint demoSpec AWire.capHashW AWire.capW ++
      (footprintGadget AWire.fpW AWire.preW AWire.postW ++
        targetGadget (AWire.capW 0) AWire.fpW AWire.cellW)) := by
  rw [systemAccepts_append, systemAccepts_append, hashConstraint_correct,
    footprint_correct, target_correct]
  decide

/-- *…the culprit named*: the membership gadget ALONE rejects the escalated
capability's hash under the authority root. -/
example : ¬ systemAccepts
    (admKeyAsg ![3, 9] 6 11 ![4, 7] ![1, 0] ![0, 1] ![9, 3] ![5, 5] ![5, 2])
    (membershipGadget demoSpec AWire.capHashW AWire.rootW (admPath 2 2 2)) := by
  rw [membership_correct]
  decide

/-- *TEETH (unauthorized — forged commitment wire)*: the same forged capability
claiming the MEMBER hash `7` on its commitment wire is REJECTED the other way. -/
example : ¬ systemAccepts
    (admKeyAsg ![3, 9] 7 11 ![4, 7] ![1, 0] ![0, 1] ![9, 3] ![5, 5] ![5, 2])
    demoAdmission := by
  rw [admission_correct]
  decide

/-- *…attribution*: membership, footprint, and target all accept the claimed wire —
the HASH constraint alone rejects (the wire is not the capability's hash). The
capability leg cannot be split: hash and membership bind the SAME commitment wire. -/
example : systemAccepts
    (admKeyAsg ![3, 9] 7 11 ![4, 7] ![1, 0] ![0, 1] ![9, 3] ![5, 5] ![5, 2])
    (membershipGadget demoSpec AWire.capHashW AWire.rootW (admPath 2 2 2) ++
      (footprintGadget AWire.fpW AWire.preW AWire.postW ++
        targetGadget (AWire.capW 0) AWire.fpW AWire.cellW)) := by
  rw [systemAccepts_append, systemAccepts_append, membership_correct,
    footprint_correct, target_correct]
  decide

/-- *…the culprit named*: the hash constraint ALONE rejects the forged wire. -/
example : ¬ systemAccepts
    (admKeyAsg ![3, 9] 7 11 ![4, 7] ![1, 0] ![0, 1] ![9, 3] ![5, 5] ![5, 2])
    (hashConstraint demoSpec AWire.capHashW AWire.capW) := by
  rw [hashConstraint_correct]
  decide

/-- *TEETH (footprint violation under FULL authority)*: the genuinely authorized
capability `(3, 8)` — hash valid, membership valid — whose turn touches the
UNDECLARED cell 9 (`5 → 4`) is REJECTED. Authority alone does not admit: the gate is
admission × footprint, and the second factor bites. -/
example : ¬ systemAccepts
    (admKeyAsg ![3, 8] 7 11 ![4, 7] ![1, 0] ![0, 1] ![9, 3] ![5, 5] ![4, 2])
    demoAdmission := by
  rw [admission_correct]
  decide

/-- *…attribution*: the whole CAPABILITY leg and the target coupling still accept
that assignment — the frame term on cell 0 alone rejects it. -/
example : systemAccepts
    (admKeyAsg ![3, 8] 7 11 ![4, 7] ![1, 0] ![0, 1] ![9, 3] ![5, 5] ![4, 2])
    (capabilityGadget demoSpec demoSpec AWire.capW AWire.capHashW AWire.rootW
        (admPath 2 2 2) ++
      targetGadget (AWire.capW 0) AWire.fpW AWire.cellW) := by
  rw [systemAccepts_append, capability_correct, target_correct]
  decide

/-- *…the culprit named*: cell 0's frame term alone rejects the out-of-footprint
touch. -/
example : ¬ accepts
    (admKeyAsg ![3, 8] 7 11 ![4, 7] ![1, 0] ![0, 1] ![9, 3] ![5, 5] ![4, 2])
    (frameTerm (AWire.fpW 0) (AWire.preW 0) (AWire.postW 0)) := by decide

/-- *TEETH (target coupling)*: the authorized capability for target 3 with a turn
DECLARING the foreign cell 9 (`fp = (1,1)`) is REJECTED — a capability admits only
turns on ITS cells, even when nothing else is wrong. -/
example : ¬ systemAccepts
    (admKeyAsg ![3, 8] 7 11 ![4, 7] ![1, 0] ![1, 1] ![9, 3] ![5, 5] ![5, 2])
    demoAdmission := by
  rw [admission_correct]
  decide

/-- *…attribution*: capability leg and footprint leg both accept the foreign
declaration — the target coupling alone rejects it. -/
example : systemAccepts
    (admKeyAsg ![3, 8] 7 11 ![4, 7] ![1, 0] ![1, 1] ![9, 3] ![5, 5] ![5, 2])
    (capabilityGadget demoSpec demoSpec AWire.capW AWire.capHashW AWire.rootW
        (admPath 2 2 2) ++
      footprintGadget AWire.fpW AWire.preW AWire.postW) := by
  rw [systemAccepts_append, capability_correct, footprint_correct]
  decide

/-- *…the culprit named*: the target term on cell 0 alone rejects the foreign
declaration (`1·(9 − 3) ≠ 0`). -/
example : ¬ accepts
    (admKeyAsg ![3, 8] 7 11 ![4, 7] ![1, 0] ![1, 1] ![9, 3] ![5, 5] ![5, 2])
    (targetTerm (AWire.fpW 0) (AWire.cellW 0) (AWire.capW 0)) := by decide

/-- *The commitment wire is FORCED, closed over the field*: EVERY accepted commitment
wire for the capability `(3, 8)` equals its hash `7` — derived from the iff, not
enumerated. -/
example (ch : ZMod 13)
    (h : systemAccepts
      (admKeyAsg ![3, 8] ch 11 ![4, 7] ![1, 0] ![0, 1] ![9, 3] ![5, 5] ![5, 2])
      demoAdmission) : ch = 7 := by
  rw [admission_correct] at h
  obtain ⟨⟨hh, -⟩, -⟩ := h
  exact hh.trans (show hashExec demoSpec ![3, 8] = 7 by decide)

/-! ### Honest scope — what is proved, and what `[ADMISSION-kernel-bridge]` must add

**Proved here**: `admission_correct` (the iff, every width/window/depth/spec), the
∃-form authority soundness (`admission_authorizes`), the frame and coupling teeth in
general form (`admission_gates_touch` / `admission_covers`), completeness
(`admission_complete`), and the keystone witnesses with per-gadget attribution. The
gate is non-vacuous with BOTH factors load-bearing: an unauthorized capability is
rejected while footprint+target accept, and a fully authorized turn is rejected the
moment it touches (or declares) outside its capability's cells.

**Named residual `[ADMISSION-kernel-bridge]`** (Assurance-side follow-on — `Compiler`
cannot import `Kernel`): the identification of `AdmissionHolds` with the kernel's
actual admission predicate over `KernelState` — authority root ↔ committed `k.caps`,
rights-word decode against the fired verb (vocabulary already on this rung:
`rangeGadget` on `capW rightsIdx`), the witnessed-window frame extended to the global
frame via the state-commitment discipline (an AIR constrains only wires it carries;
cells outside the window stand still because the state root reopens footprint cells
only), and `ι = N` cross-incidence footprint disjointness (`Σᵢ fpᵃᵢ·fpᵇᵢ ≐ 0`,
expressible in this DSL). Floors inherited, never claimed: `[COMMIT-CR]` (forged
membership needs a collision), `[AIR-poseidon-params]` (deployed hash parameters).
`[AIR-flatten]`/`[AIR-sumcheck]`/`[EMIT-*]` unchanged upstream — `Compiler/Emit`
consumes this system like any other, which is exactly what makes the emitted object
the kernel's gated executor, DERIVED. -/

end Minidregg.Compiler
