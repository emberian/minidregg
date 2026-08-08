/-
# `Compiler/EmitShare.lean` — [EMIT-share] CLOSED: hash-consing CSE on the emitted
descriptor, a PASS with its own faithfulness theorem

**Substrate, said out loud: the sharing pass is Lean-AUTHORED and its faithfulness is a
THEOREM over the actual transformed descriptor.** `flatten` serializes the term TREE, so
duplicated subterms emit duplicated gates — the demo note-spend measures 2,696,666 gates
(`Emit` §8). `cse` recovers the DAG: ONE forward walk carrying a wire-substitution and a
gate-signature table; a gate whose (op, rewritten-inputs) signature was already emitted is
DROPPED and its output wire remapped to the earlier gate's, so sharing propagates bottom-up
(the second copy of a whole subtree collapses gate by gate). NOT a hand-optimization of an
emitted list: a total function `ConstraintDescriptor F → ConstraintDescriptor F`, with the
faithfulness proved about the pass itself.

## The construction

* `cseGo` — the walk. State: `subst` (wire ↦ its kept representative; efficient
  `Std.HashMap`, absent = itself), `sigs` (gate signature ↦ representative output wire),
  `kept` (the surviving gates, inputs already rewritten). Per gate: rewrite inputs through
  `subst`; if the signature is in `sigs`, drop the gate and bind `out ↦` the representative;
  else keep it and record its signature.
* `cse` — run the walk over `d.gates`, rewrite `d.zeros` through the final substitution.
  Header fields unchanged (the WIRE numbering is kept; only the gate LIST shrinks —
  `[EMIT-share-compact]` below).
* `cseSubst` — the final wire-remapping, exposed so the backward theorem can NAME the
  witness transport.

## The faithfulness (what is PROVED, and in which direction)

* `cse_holds` — forward, UNCONDITIONAL: EVERY total wire vector satisfying `d` satisfies
  `cse d` — the SAME vector, no remapping (a dropped gate's wire already carries the same
  value as its representative, because both gates held). One induction (`cseGo_forward`).
* `holds_of_cse_holds` — backward, under `d.SSA`: a vector `wv'` satisfying `cse d` yields
  `wv' ∘ cseSubst d` satisfying `d` — the shared wire's value is pulled back to every wire
  that was remapped onto it. One induction (`cseGo_backward`).
* `cse_faithful` — the satisfiability-equivalence, both directions packaged:
  `(∃ wv, descriptorHolds d wv) ↔ (∃ wv', descriptorHolds (cse d) wv')` for SSA `d`.
* `emit_ssa` — EVERY emitted descriptor is SSA (gate inputs read only wires strictly below
  their own output — `flattenSystem_scoped` through the layout — and outputs are strictly
  increasing in list order — `flatten_gates_sorted`, the allocation order made explicit).
  So the deployed path is fully covered, no hypothesis left at the use site:
* `cse_emit_accepts_iff` — **the seam, re-closed THROUGH the CSE**: a total wire vector
  pinning the variable wires satisfies `cse (emit …)` IFF `systemAccepts` — the prover on
  the SMALL descriptor proves exactly the statement the big one meant.

## Why `SSA` is REAL (the backward direction is FALSE without it)

Forward needs nothing. Backward genuinely needs the emitted shape; two counterexamples the
proof must (and does) exclude, both violating SSA:

* re-bound output: gates `w₁₀ = 1`, `w₁₁ = 2`, `w₅ = 1` (dup of the first, dropped,
  `5 ↦ 10`), `w₅ = 2` (dup of the second, dropped, `5 ↦ 11`). The original forces
  `wv 5 = 1 ∧ wv 5 = 2` — UNSAT; the CSE'd descriptor kept only `w₁₀ = 1, w₁₁ = 2` — SAT.
  Excluded by outputs-strictly-increasing (no output bound twice).
* consumer before producer: gates `w₀ = w₅`, `w₁ = 1`, `w₅ = 1` (dropped, `5 ↦ 1`) with
  zero-check on `w₀`. Original: `wv 5 = 1`, `wv 0 = wv 5 = 1 ≠ 0` — UNSAT; CSE'd: the first
  gate still reads the RAW `w₅` (the substitution did not exist yet), now unconstrained —
  SAT. Excluded by inputs-below-own-output + sortedness (producers precede consumers).

## Keystones (BUILT, `ZMod 7` / `ZMod 13`)

`exShared = (x+2)·(x+2)` — the same subterm twice; its emitted descriptor duplicates the
add gate, `cse` merges it (3 gates → 2, measured §6). Satisfiable: the honest vector
transfers through `cse_holds` (decided on the ORIGINAL descriptor — the kernel does not
reduce `Std.HashMap`, honestly said, so every keystone is THEOREM-mediated and `decide`
runs only on descriptors/acceptance the kernel can chew). Teeth: at `x = 3` NO total wire
vector satisfies the CSE'd descriptor (via the re-closed seam), and the specific violating
vector fails as its corollary. The note-spend: same pair of witnesses at the deployed
descriptor (§9), gate count measured 2,696,666 → 220.

## Residuals (named, none stubbed)

* `[EMIT-share-compact]` — `cse` shrinks the gate LIST, not the wire NUMBERING: `nWires`
  still counts the dropped aux wires (they are simply unconstrained), and gates whose
  outputs become unreferenced are kept. A renumbering/dead-gate sweep is a further derived
  rung with the same theorem shape. The PROVER cost is driven by the gate count, which is
  what shrank.
* Sharing is STRUCTURAL (hash-consing): `a+b` and `b+a` do not merge, no algebraic
  identities — that is a rewriting rung, not this one.
* `[EMIT-backend]` / `[EMIT-sound]` — unchanged, inherited from `Emit`: the prover that
  consumes the (now smaller) descriptor is unverified compute; its acceptance claim still
  rides the FRI/STARK floor.
-/
import Compiler.Emit
import Std.Data.HashMap.Lemmas

namespace Minidregg.Compiler

universe u

variable {F : Type u} {Idx : Type u}

/-! ## §1. The signature table's key, and the pass. -/

instance : Hashable GateOp := ⟨fun | .add => 0 | .mul => 1⟩

instance [Hashable F] : Hashable (DWire F) :=
  ⟨fun | .cnst c => mixHash 0 (hash c) | .wire n => mixHash 1 (hash n)⟩

/-- A gate's SHARING SIGNATURE: operation and (rewritten) operands — everything except the
output wire. Two gates with the same signature are forced to the same value. -/
abbrev GateSig (F : Type u) : Type u := GateOp × DWire F × DWire F

/-- Rewrite one operand through the substitution: a wire is replaced by its representative
(absent = itself), constants pass through. -/
def DWire.subst (σ : Std.HashMap ℕ ℕ) : DWire F → DWire F
  | .cnst c => .cnst c
  | .wire n => .wire (σ.getD n n)

section Pass

variable [DecidableEq F] [Hashable F]

/-- The pass state: the wire substitution, the signature table, and the kept gates
(prepended; `cse` reverses once at the end, so the emitted order — producers before
consumers — survives). -/
structure CseState (F : Type u) [DecidableEq F] [Hashable F] : Type u where
  subst : Std.HashMap ℕ ℕ
  sigs : Std.HashMap (GateSig F) ℕ
  kept : List (DGate F)

/-- **The walk** — one pass, left to right: rewrite the gate's inputs through the current
substitution; a signature hit DROPS the gate (its output wire remapped onto the
representative), a miss KEEPS the rewritten gate and records its signature. -/
def cseGo : List (DGate F) → CseState F → CseState F
  | [], s => s
  | g :: gs, s =>
      match s.sigs[((g.op, g.a.subst s.subst, g.b.subst s.subst) : GateSig F)]? with
      | some w => cseGo gs ⟨s.subst.insert g.out w, s.sigs, s.kept⟩
      | none => cseGo gs ⟨s.subst,
          s.sigs.insert (g.op, g.a.subst s.subst, g.b.subst s.subst) g.out,
          ⟨g.op, g.a.subst s.subst, g.b.subst s.subst, g.out⟩ :: s.kept⟩

/-- **The CSE pass**: dedup the gates, rewrite the zero-checks through the final
substitution. Header fields unchanged. -/
def cse (d : ConstraintDescriptor F) : ConstraintDescriptor F :=
  let s := cseGo d.gates ⟨∅, ∅, []⟩
  { d with
    gates := s.kept.reverse
    zeros := d.zeros.map (DWire.subst s.subst) }

/-- The final wire-remapping of the pass on `d` — the witness transport of the backward
faithfulness direction. -/
def cseSubst (d : ConstraintDescriptor F) : ℕ → ℕ :=
  fun n => (cseGo d.gates ⟨∅, ∅, []⟩).subst.getD n n

theorem cse_gates (d : ConstraintDescriptor F) :
    (cse d).gates = (cseGo d.gates ⟨∅, ∅, []⟩).kept.reverse := rfl

theorem cse_zeros (d : ConstraintDescriptor F) :
    (cse d).zeros = d.zeros.map (DWire.subst (cseGo d.gates ⟨∅, ∅, []⟩).subst) := rfl

@[simp] theorem cse_nPublic (d : ConstraintDescriptor F) : (cse d).nPublic = d.nPublic := rfl
@[simp] theorem cse_nVars (d : ConstraintDescriptor F) : (cse d).nVars = d.nVars := rfl
@[simp] theorem cse_nWires (d : ConstraintDescriptor F) : (cse d).nWires = d.nWires := rfl

theorem cseGo_cons (g : DGate F) (gs : List (DGate F)) (s : CseState F) :
    cseGo (g :: gs) s =
      match s.sigs[((g.op, g.a.subst s.subst, g.b.subst s.subst) : GateSig F)]? with
      | some w => cseGo gs ⟨s.subst.insert g.out w, s.sigs, s.kept⟩
      | none => cseGo gs ⟨s.subst,
          s.sigs.insert (g.op, g.a.subst s.subst, g.b.subst s.subst) g.out,
          ⟨g.op, g.a.subst s.subst, g.b.subst s.subst, g.out⟩ :: s.kept⟩ := rfl

/-! ## §2. Structural facts about the walk — map-lemma plumbing, then three inductions. -/

private theorem getD_insert_self {α : Type*} {β : Type*} [BEq α] [Hashable α] [LawfulBEq α]
    {m : Std.HashMap α β} {k : α} {v fb : β} : (m.insert k v).getD k fb = v := by
  rw [Std.HashMap.getD_insert, if_pos (by simp)]

private theorem getD_insert_ne {α : Type*} {β : Type*} [BEq α] [Hashable α] [LawfulBEq α]
    {m : Std.HashMap α β} {k a : α} {v fb : β} (h : k ≠ a) :
    (m.insert k v).getD a fb = m.getD a fb := by
  rw [Std.HashMap.getD_insert, if_neg (by simpa using h)]

private theorem getElem?_insert_ne {α : Type*} {β : Type*} [BEq α] [Hashable α] [LawfulBEq α]
    {m : Std.HashMap α β} {k a : α} {v : β} (h : k ≠ a) :
    (m.insert k v)[a]? = m[a]? := by
  rw [Std.HashMap.getElem?_insert, if_neg (by simpa using h)]

/-- Kept gates only accumulate: anything kept survives the rest of the walk. -/
theorem cseGo_kept_mono (gs : List (DGate F)) : ∀ (s : CseState F) (k : DGate F),
    k ∈ s.kept → k ∈ (cseGo gs s).kept := by
  induction gs with
  | nil => intro s k hk; exact hk
  | cons g gs ih =>
    intro s k hk
    cases hl : s.sigs[((g.op, g.a.subst s.subst, g.b.subst s.subst) : GateSig F)]? with
    | some w => simp only [cseGo_cons, hl]; exact ih _ k hk
    | none => simp only [cseGo_cons, hl]; exact ih _ k (List.mem_cons_of_mem _ hk)

/-- The walk binds only wires that are outputs of the gates it processes: any other wire's
representative is untouched. -/
theorem cseGo_subst_stable (gs : List (DGate F)) : ∀ (s : CseState F) (x : ℕ),
    (∀ g ∈ gs, x ≠ g.out) →
    (cseGo gs s).subst.getD x x = s.subst.getD x x := by
  induction gs with
  | nil => intro s x _; rfl
  | cons g gs ih =>
    intro s x hx
    cases hl : s.sigs[((g.op, g.a.subst s.subst, g.b.subst s.subst) : GateSig F)]? with
    | some w =>
      simp only [cseGo_cons, hl]
      exact (ih _ x fun g' hg' => hx g' (List.mem_cons_of_mem _ hg')).trans
        (getD_insert_ne (hx g (List.mem_cons_self ..)).symm)
    | none =>
      simp only [cseGo_cons, hl]
      exact ih _ x fun g' hg' => hx g' (List.mem_cons_of_mem _ hg')

/-- The signature-table invariant survives an insert-and-keep step: a hit names a gate that
is genuinely in the kept list. -/
private theorem sig_insert_spec {sigs : Std.HashMap (GateSig F) ℕ} {kept : List (DGate F)}
    (hsig : ∀ op a b w, sigs[((op, a, b) : GateSig F)]? = some w →
      (⟨op, a, b, w⟩ : DGate F) ∈ kept)
    (op₀ : GateOp) (a₀ b₀ : DWire F) (o₀ : ℕ) :
    ∀ op a b w, (sigs.insert (op₀, a₀, b₀) o₀)[((op, a, b) : GateSig F)]? = some w →
      (⟨op, a, b, w⟩ : DGate F) ∈ (⟨op₀, a₀, b₀, o₀⟩ : DGate F) :: kept := by
  intro op a b w hlk
  rw [Std.HashMap.getElem?_insert] at hlk
  split at hlk
  · next hbeq =>
    have heq : ((op₀, a₀, b₀) : GateSig F) = (op, a, b) := eq_of_beq hbeq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    obtain rfl := Option.some.inj hlk
    exact List.mem_cons_self ..
  · next => exact List.mem_cons_of_mem _ (hsig op a b w hlk)

/-! ## §3. Reads through the substitution. -/

omit [DecidableEq F] [Hashable F] in
theorem DWire.subst_read {σ : Std.HashMap ℕ ℕ} {wv : ℕ → F}
    (hσ : ∀ x, wv (σ.getD x x) = wv x) : ∀ w : DWire F, (w.subst σ).read wv = w.read wv
  | .cnst _ => rfl
  | .wire n => hσ n

omit [DecidableEq F] [Hashable F] in
theorem DWire.read_subst_comp (σ : Std.HashMap ℕ ℕ) (wv' : ℕ → F) :
    ∀ w : DWire F, w.read (fun n => wv' (σ.getD n n)) = (w.subst σ).read wv'
  | .cnst _ => rfl
  | .wire _ => rfl

omit [DecidableEq F] [Hashable F] in
/-- A bounded operand's read through the pulled-back vector is its rewritten form's read,
whenever the two substitutions agree below the bound. -/
theorem DWire.read_transfer {σ₁ σ₂ : Std.HashMap ℕ ℕ} {wv' : ℕ → F} {bound : ℕ}
    (h : ∀ m, m < bound → σ₂.getD m m = σ₁.getD m m) :
    ∀ {w : DWire F}, w.bounded bound →
      w.read (fun n => wv' (σ₂.getD n n)) = (w.subst σ₁).read wv'
  | .cnst _, _ => rfl
  | .wire m, hw => congrArg wv' (h m hw)

/-! ## §4. `cseGo_forward` — the forward direction, UNCONDITIONAL.

Any total wire vector satisfying the input gates satisfies the kept gates — the SAME
vector. The invariant carried: the vector cannot tell a wire from its representative
(`wv ∘ subst = wv` pointwise), because a gate is only dropped when its representative is
forced to the same value. -/

variable [Field F]

theorem cseGo_forward (wv : ℕ → F) (gs : List (DGate F)) : ∀ (s : CseState F),
    (∀ x, wv (s.subst.getD x x) = wv x) →
    (∀ k ∈ s.kept, k.holds wv) →
    (∀ op a b w, s.sigs[((op, a, b) : GateSig F)]? = some w →
      (⟨op, a, b, w⟩ : DGate F) ∈ s.kept) →
    (∀ g ∈ gs, g.holds wv) →
    (∀ k ∈ (cseGo gs s).kept, k.holds wv) ∧
      ∀ x, wv ((cseGo gs s).subst.getD x x) = wv x := by
  induction gs with
  | nil => intro s hσ hkept _ _; exact ⟨hkept, hσ⟩
  | cons g gs ih =>
    intro s hσ hkept hsig hgs
    have hg : g.op.denote (g.a.read wv) (g.b.read wv) = wv g.out :=
      hgs g (List.mem_cons_self ..)
    have hga : (g.a.subst s.subst).read wv = g.a.read wv := DWire.subst_read hσ g.a
    have hgb : (g.b.subst s.subst).read wv = g.b.read wv := DWire.subst_read hσ g.b
    cases hl : s.sigs[((g.op, g.a.subst s.subst, g.b.subst s.subst) : GateSig F)]? with
    | some w =>
      simp only [cseGo_cons, hl]
      have hkh : g.op.denote ((g.a.subst s.subst).read wv) ((g.b.subst s.subst).read wv)
          = wv w := hkept _ (hsig _ _ _ _ hl)
      have hval : wv w = wv g.out := by rw [← hkh, hga, hgb]; exact hg
      refine ih _ ?_ hkept hsig fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
      intro x
      show wv ((s.subst.insert g.out w).getD x x) = wv x
      by_cases hx : g.out = x
      · subst hx
        rw [getD_insert_self]
        exact hval
      · rw [getD_insert_ne hx]
        exact hσ x
    | none =>
      simp only [cseGo_cons, hl]
      refine ih _ hσ ?_ (sig_insert_spec hsig _ _ _ _)
        fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk'
      · show g.op.denote ((g.a.subst s.subst).read wv) ((g.b.subst s.subst).read wv)
          = wv g.out
        rw [hga, hgb]; exact hg
      · exact hkept k hk'

/-! ## §5. SSA, and `cseGo_backward` — the backward direction.

SSA is the emitted shape: gate inputs read only wires strictly below their own output, and
outputs strictly increase along the list (so no output is bound twice and every reference
to a wire comes AFTER its producer). Under it, the final substitution agrees with the
substitution at each gate's processing time on everything the gate mentions — the
stability that lets one vector `wv' ∘ cseSubst` satisfy every original gate. The header's
two counterexamples show both SSA components are LOAD-BEARING. -/

end Pass

/-- **SSA** — the emitted-descriptor shape: inputs strictly below own output, outputs
strictly increasing in list order. `emit_ssa` (§6) proves every emitted descriptor has it. -/
def ConstraintDescriptor.SSA (d : ConstraintDescriptor F) : Prop :=
  (∀ g ∈ d.gates, g.a.bounded g.out ∧ g.b.bounded g.out) ∧
    d.gates.Pairwise (fun g₁ g₂ => g₁.out < g₂.out)

section Faithful

variable [DecidableEq F] [Hashable F] [Field F]

theorem cseGo_backward (wv' : ℕ → F) (gs : List (DGate F)) : ∀ (s : CseState F),
    (∀ g ∈ gs, g.a.bounded g.out ∧ g.b.bounded g.out) →
    gs.Pairwise (fun g₁ g₂ => g₁.out < g₂.out) →
    (∀ g ∈ gs, s.subst[g.out]? = none) →
    (∀ op a b w, s.sigs[((op, a, b) : GateSig F)]? = some w →
      (⟨op, a, b, w⟩ : DGate F) ∈ s.kept) →
    (∀ k ∈ (cseGo gs s).kept, k.holds wv') →
    ∀ g ∈ gs, g.holds fun n => wv' ((cseGo gs s).subst.getD n n) := by
  induction gs with
  | nil => intro s _ _ _ _ _ g hg; exact nomatch hg
  | cons g gs ih =>
    intro s hssa hsorted hfresh hsig hkept
    have hlt : ∀ g' ∈ gs, g.out < g'.out := (List.pairwise_cons.mp hsorted).1
    have htail := (List.pairwise_cons.mp hsorted).2
    obtain ⟨hba, hbb⟩ := hssa g (List.mem_cons_self ..)
    cases hl : s.sigs[((g.op, g.a.subst s.subst, g.b.subst s.subst) : GateSig F)]? with
    | some w =>
      simp only [cseGo_cons, hl] at hkept ⊢
      have hstab : ∀ m, m < g.out →
          (cseGo gs ⟨s.subst.insert g.out w, s.sigs, s.kept⟩).subst.getD m m
            = s.subst.getD m m := fun m hm =>
        (cseGo_subst_stable gs _ m fun g' hg' =>
            Nat.ne_of_lt (hm.trans (hlt g' hg'))).trans
          (getD_insert_ne (ne_of_gt hm))
      have hout : (cseGo gs ⟨s.subst.insert g.out w, s.sigs, s.kept⟩).subst.getD
          g.out g.out = w :=
        (cseGo_subst_stable gs _ g.out fun g' hg' =>
          Nat.ne_of_lt (hlt g' hg')).trans getD_insert_self
      intro g₀ hg₀
      rcases List.mem_cons.mp hg₀ with rfl | hg₀'
      · have hkh : g₀.op.denote ((g₀.a.subst s.subst).read wv')
            ((g₀.b.subst s.subst).read wv') = wv' w :=
          hkept _ (cseGo_kept_mono gs _ _ (hsig _ _ _ _ hl))
        show g₀.op.denote
            (g₀.a.read fun n =>
              wv' ((cseGo gs ⟨s.subst.insert g₀.out w, s.sigs, s.kept⟩).subst.getD n n))
            (g₀.b.read fun n =>
              wv' ((cseGo gs ⟨s.subst.insert g₀.out w, s.sigs, s.kept⟩).subst.getD n n))
          = wv' ((cseGo gs ⟨s.subst.insert g₀.out w, s.sigs, s.kept⟩).subst.getD
              g₀.out g₀.out)
        rw [DWire.read_transfer hstab hba, DWire.read_transfer hstab hbb, hout]
        exact hkh
      · exact ih ⟨s.subst.insert g.out w, s.sigs, s.kept⟩
          (fun g' hg' => hssa g' (List.mem_cons_of_mem _ hg')) htail
          (fun g' hg' => (getElem?_insert_ne (Nat.ne_of_lt (hlt g' hg'))).trans
            (hfresh g' (List.mem_cons_of_mem _ hg')))
          hsig hkept g₀ hg₀'
    | none =>
      simp only [cseGo_cons, hl] at hkept ⊢
      have hstab : ∀ m, m < g.out →
          (cseGo gs ⟨s.subst,
              s.sigs.insert (g.op, g.a.subst s.subst, g.b.subst s.subst) g.out,
              ⟨g.op, g.a.subst s.subst, g.b.subst s.subst, g.out⟩ :: s.kept⟩).subst.getD m m
            = s.subst.getD m m := fun m hm =>
        cseGo_subst_stable gs _ m fun g' hg' => Nat.ne_of_lt (hm.trans (hlt g' hg'))
      have hout : (cseGo gs ⟨s.subst,
            s.sigs.insert (g.op, g.a.subst s.subst, g.b.subst s.subst) g.out,
            ⟨g.op, g.a.subst s.subst, g.b.subst s.subst, g.out⟩ :: s.kept⟩).subst.getD
          g.out g.out = g.out :=
        (cseGo_subst_stable gs _ g.out fun g' hg' => Nat.ne_of_lt (hlt g' hg')).trans
          (by show s.subst.getD g.out g.out = g.out
              rw [Std.HashMap.getD_eq_getD_getElem?, hfresh g (List.mem_cons_self ..)]
              rfl)
      intro g₀ hg₀
      rcases List.mem_cons.mp hg₀ with rfl | hg₀'
      · have hkh : g₀.op.denote ((g₀.a.subst s.subst).read wv')
            ((g₀.b.subst s.subst).read wv') = wv' g₀.out :=
          hkept _ (cseGo_kept_mono gs _ _ (List.mem_cons_self ..))
        show g₀.op.denote
            (g₀.a.read fun n =>
              wv' ((cseGo gs ⟨s.subst,
                s.sigs.insert (g₀.op, g₀.a.subst s.subst, g₀.b.subst s.subst) g₀.out,
                ⟨g₀.op, g₀.a.subst s.subst, g₀.b.subst s.subst, g₀.out⟩ ::
                  s.kept⟩).subst.getD n n))
            (g₀.b.read fun n =>
              wv' ((cseGo gs ⟨s.subst,
                s.sigs.insert (g₀.op, g₀.a.subst s.subst, g₀.b.subst s.subst) g₀.out,
                ⟨g₀.op, g₀.a.subst s.subst, g₀.b.subst s.subst, g₀.out⟩ ::
                  s.kept⟩).subst.getD n n))
          = wv' ((cseGo gs ⟨s.subst,
              s.sigs.insert (g₀.op, g₀.a.subst s.subst, g₀.b.subst s.subst) g₀.out,
              ⟨g₀.op, g₀.a.subst s.subst, g₀.b.subst s.subst, g₀.out⟩ ::
                s.kept⟩).subst.getD g₀.out g₀.out)
        rw [DWire.read_transfer hstab hba, DWire.read_transfer hstab hbb, hout]
        exact hkh
      · exact ih ⟨s.subst,
            s.sigs.insert (g.op, g.a.subst s.subst, g.b.subst s.subst) g.out,
            ⟨g.op, g.a.subst s.subst, g.b.subst s.subst, g.out⟩ :: s.kept⟩
          (fun g' hg' => hssa g' (List.mem_cons_of_mem _ hg')) htail
          (fun g' hg' => hfresh g' (List.mem_cons_of_mem _ hg'))
          (sig_insert_spec hsig _ _ _ _) hkept g₀ hg₀'

/-! ## §5b. The faithfulness, packaged. -/

/-- **Forward faithfulness — UNCONDITIONAL, same witness.** Every total wire vector
satisfying `d` satisfies `cse d`. The prover's honest witness survives the pass untouched. -/
theorem cse_holds (d : ConstraintDescriptor F) (wv : ℕ → F)
    (h : descriptorHolds d wv) : descriptorHolds (cse d) wv := by
  obtain ⟨hg, hz⟩ := h
  have hσ0 : ∀ x, wv (((⟨∅, ∅, []⟩ : CseState F).subst).getD x x) = wv x := by
    intro x
    show wv ((∅ : Std.HashMap ℕ ℕ).getD x x) = wv x
    rw [Std.HashMap.getD_empty]
  have hsig0 : ∀ op a b w,
      ((⟨∅, ∅, []⟩ : CseState F).sigs)[((op, a, b) : GateSig F)]? = some w →
      (⟨op, a, b, w⟩ : DGate F) ∈ (⟨∅, ∅, []⟩ : CseState F).kept := by
    intro op a b w hlk
    rw [show ((⟨∅, ∅, []⟩ : CseState F).sigs) = (∅ : Std.HashMap (GateSig F) ℕ) from rfl,
      Std.HashMap.getElem?_empty] at hlk
    exact nomatch hlk
  obtain ⟨hkept, hσ⟩ := cseGo_forward wv d.gates ⟨∅, ∅, []⟩ hσ0
    (fun k hk => nomatch hk) hsig0 hg
  refine ⟨fun g hgm => ?_, fun z hzm => ?_⟩
  · exact hkept g (List.mem_reverse.mp hgm)
  · obtain ⟨z₀, hz₀, rfl⟩ := List.mem_map.mp (show z ∈ d.zeros.map
        (DWire.subst (cseGo d.gates ⟨∅, ∅, []⟩).subst) from hzm)
    rw [DWire.subst_read hσ]
    exact hz z₀ hz₀

/-- **Backward faithfulness — under SSA, witness transported through `cseSubst`.** A vector
satisfying the CSE'd descriptor pulls back along the wire-remapping to a vector satisfying
the original: the shared wire's value is copied onto every wire that was merged into it. -/
theorem holds_of_cse_holds (d : ConstraintDescriptor F) (hssa : d.SSA) (wv' : ℕ → F)
    (h : descriptorHolds (cse d) wv') :
    descriptorHolds d fun n => wv' (cseSubst d n) := by
  obtain ⟨hg', hz'⟩ := h
  have hfresh0 : ∀ g ∈ d.gates, ((⟨∅, ∅, []⟩ : CseState F).subst)[g.out]? = none := by
    intro g _
    show (∅ : Std.HashMap ℕ ℕ)[g.out]? = none
    exact Std.HashMap.getElem?_empty
  have hsig0 : ∀ op a b w,
      ((⟨∅, ∅, []⟩ : CseState F).sigs)[((op, a, b) : GateSig F)]? = some w →
      (⟨op, a, b, w⟩ : DGate F) ∈ (⟨∅, ∅, []⟩ : CseState F).kept := by
    intro op a b w hlk
    rw [show ((⟨∅, ∅, []⟩ : CseState F).sigs) = (∅ : Std.HashMap (GateSig F) ℕ) from rfl,
      Std.HashMap.getElem?_empty] at hlk
    exact nomatch hlk
  have hkept : ∀ k ∈ (cseGo d.gates ⟨∅, ∅, []⟩).kept, k.holds wv' := fun k hk =>
    hg' k (List.mem_reverse.mpr hk)
  refine ⟨cseGo_backward wv' d.gates ⟨∅, ∅, []⟩ hssa.1 hssa.2 hfresh0 hsig0 hkept,
    fun z hzm => ?_⟩
  show z.read (fun n => wv' ((cseGo d.gates ⟨∅, ∅, []⟩).subst.getD n n)) = 0
  rw [DWire.read_subst_comp]
  exact hz' _ (List.mem_map.mpr ⟨z, hzm, rfl⟩)

/-- **`cse_faithful` — the keystone: satisfiability-equivalence.** For an SSA descriptor
(every emitted one, `emit_ssa`), the CSE'd descriptor is satisfiable IFF the original is —
forward with the SAME witness, backward through the wire-remapping. The prover on the small
descriptor proves the same statement. -/
theorem cse_faithful (d : ConstraintDescriptor F) (hssa : d.SSA) :
    (∃ wv : ℕ → F, descriptorHolds d wv) ↔
      ∃ wv' : ℕ → F, descriptorHolds (cse d) wv' :=
  ⟨fun ⟨wv, h⟩ => ⟨wv, cse_holds d wv h⟩,
   fun ⟨wv', h⟩ => ⟨fun n => wv' (cseSubst d n), holds_of_cse_holds d hssa wv' h⟩⟩

end Faithful

/-! ## §6. Emitted descriptors are SSA — the hypothesis discharged at the deployed shape.

`flattenSystem_scoped` (REUSED) already gives inputs-below-own-output; what was implicit is
that the gate LIST is in allocation order. Two inductions mirroring `flatten_scoped`'s
structure make it explicit, and the layout (`+ nVars`) preserves it. -/

section EmitSSA

variable [Field F]

omit [Field F] in
/-- The flattened gates of one term are in strict allocation order. -/
theorem flatten_gates_sorted (t : Term (AirSig F Idx)) (n₀ : ℕ) :
    (flatten t n₀).gates.Pairwise (fun g₁ g₂ => g₁.out < g₂.out) := by
  induction t generalizing n₀ with
  | mk s k ih =>
    cases s with
    | const c => exact List.Pairwise.nil
    | var i => exact List.Pairwise.nil
    | add | mul =>
      obtain ⟨hle₁, -, hgl⟩ := flatten_scoped (k false) n₀
      obtain ⟨hle₂, -, hgr⟩ := flatten_scoped (k true) (flatten (k false) n₀).next
      simp only [flatten_mk_add, flatten_mk_mul]
      refine List.pairwise_append.mpr ⟨List.pairwise_append.mpr
        ⟨ih false n₀, ih true (flatten (k false) n₀).next, ?_⟩, ?_, ?_⟩
      · intro g₁ hg₁ g₂ hg₂
        have h₁ := (hgl g₁ hg₁).2.2.2
        have h₂ := (hgr g₂ hg₂).2.2.1
        show g₁.out < g₂.out
        omega
      · simp
      · intro g₁ hg₁ g₂ hg₂
        obtain rfl := List.mem_singleton.mp hg₂
        show g₁.out < (flatten (k true) (flatten (k false) n₀).next).next
        rcases List.mem_append.mp hg₁ with h | h
        · have := (hgl g₁ h).2.2.2
          omega
        · have := (hgr g₁ h).2.2.2
          omega

omit [Field F] in
/-- The whole flattened system's gates are in strict allocation order. -/
theorem flattenSystem_gates_sorted (s : ConstraintSystem F Idx) (n₀ : ℕ) :
    (flattenSystem s n₀).gates.Pairwise (fun g₁ g₂ => g₁.out < g₂.out) := by
  induction s generalizing n₀ with
  | nil => exact List.Pairwise.nil
  | cons t ts ih =>
    rw [flattenSystem_cons_gates]
    obtain ⟨-, -, hgl⟩ := flatten_scoped t n₀
    obtain ⟨-, -, hgr⟩ := flattenSystem_scoped ts (flatten t n₀).next
    refine List.pairwise_append.mpr ⟨flatten_gates_sorted t n₀, ih _, ?_⟩
    intro g₁ hg₁ g₂ hg₂
    have h₁ := (hgl g₁ hg₁).2.2.2
    have h₂ := (hgr g₂ hg₂).2.2.1
    show g₁.out < g₂.out
    omega

omit [Field F] in
/-- Every emitted gate output sits in the aux region: at or above `nVars`. -/
theorem emit_out_ge (ix : Idx → ℕ) (nPublic nVars : ℕ) (s : ConstraintSystem F Idx) :
    ∀ g ∈ (emit ix nPublic nVars s).gates, nVars ≤ g.out := by
  intro g hg
  obtain ⟨g₀, -, rfl⟩ := List.mem_map.mp hg
  exact Nat.le_add_right _ _

omit [Field F] in
/-- **Every emitted descriptor is SSA** (in-range layout): inputs below own output through
the layout (`emitWire_bounded` at `N = nVars + g.out`, REUSED), outputs strictly increasing
(the allocation order, mapped). The backward faithfulness hypothesis holds at every
deployed descriptor. -/
theorem emit_ssa (ix : Idx → ℕ) (nPublic nVars : ℕ) (hbound : ∀ i, ix i < nVars)
    (s : ConstraintSystem F Idx) : (emit ix nPublic nVars s).SSA := by
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
    obtain ⟨-, -, hsc⟩ := flattenSystem_scoped s 0
    obtain ⟨ha, hb, -, -⟩ := hsc g₀ hg₀
    exact ⟨emitWire_bounded ix hbound le_rfl ha, emitWire_bounded ix hbound le_rfl hb⟩
  · show ((flattenSystem s 0).gates.map (emitGate ix nVars)).Pairwise
      (fun g₁ g₂ => g₁.out < g₂.out)
    exact List.pairwise_map.mpr ((flattenSystem_gates_sorted s 0).imp
      fun h => Nat.add_lt_add_left h nVars)

end EmitSSA

/-! ## §7. The seam, re-closed THROUGH the CSE. -/

section Seam

variable [DecidableEq F] [Hashable F] [Field F]

omit [Field F] in
/-- The pass never remaps a wire that is no gate's output — in particular, never a
variable wire of an emitted descriptor. -/
theorem cseSubst_eq_self (d : ConstraintDescriptor F) (x : ℕ)
    (hx : ∀ g ∈ d.gates, x ≠ g.out) : cseSubst d x = x := by
  show (cseGo d.gates ⟨∅, ∅, []⟩).subst.getD x x = x
  rw [cseGo_subst_stable d.gates _ x hx]
  exact Std.HashMap.getD_empty

/-- **`cse_emit_accepts_iff` — the emit path, CSE'd, end to end.** For an injective
in-range layout: SOME total wire vector pinning the variable wires to `asg` satisfies the
CSE'd emitted descriptor IFF the constraint system accepts `asg` — `emit_accepts_iff`
(REUSED) chained through the faithfulness, the SSA hypothesis discharged by `emit_ssa`,
and the pinning preserved because variable wires are never remapped. The prover that
checks the SMALL descriptor proves the SAME statement the big one meant. -/
theorem cse_emit_accepts_iff (ix : Idx → ℕ) (hinj : Function.Injective ix)
    (nPublic nVars : ℕ) (hbound : ∀ i, ix i < nVars)
    (asg : Idx → F) (s : ConstraintSystem F Idx) :
    (∃ wv : ℕ → F, (∀ i, wv (ix i) = asg i) ∧
        descriptorHolds (cse (emit ix nPublic nVars s)) wv)
      ↔ systemAccepts asg s := by
  rw [← emit_accepts_iff ix hinj nPublic nVars hbound asg s]
  constructor
  · rintro ⟨wv, hpin, hd⟩
    refine ⟨fun n => wv (cseSubst (emit ix nPublic nVars s) n), fun i => ?_,
      holds_of_cse_holds _ (emit_ssa ix nPublic nVars hbound s) wv hd⟩
    have hne : ∀ g ∈ (emit ix nPublic nVars s).gates, ix i ≠ g.out := fun g hg => by
      have h₁ := emit_out_ge ix nPublic nVars s g hg
      have h₂ := hbound i
      omega
    show wv (cseSubst (emit ix nPublic nVars s) (ix i)) = asg i
    rw [cseSubst_eq_self _ _ hne]
    exact hpin i
  · rintro ⟨wv, hpin, hd⟩
    exact ⟨wv, hpin, cse_holds _ wv hd⟩

/-- The seam at the canonical `Fin m` layout (`Type`-level field, as in
`emit_accepts_iff_fin`). -/
theorem cse_emit_accepts_iff_fin {K : Type} [Field K] [DecidableEq K] [Hashable K]
    (m nPublic : ℕ) (asg : Fin m → K) (s : ConstraintSystem K (Fin m)) :
    (∃ wv : ℕ → K, (∀ i : Fin m, wv i.val = asg i) ∧
        descriptorHolds (cse (emit Fin.val nPublic m s)) wv)
      ↔ systemAccepts asg s :=
  cse_emit_accepts_iff Fin.val Fin.val_injective nPublic m (fun i => i.isLt) asg s

end Seam

/-! ## §8. Keystone witnesses, BUILT — `ZMod 7`, a genuinely SHARED subterm.

`exShared = (x+2)·(x+2)`: the same subterm twice, so the tree-flatten emits the add gate
TWICE. Every keystone is THEOREM-mediated with `decide` only on objects the kernel reduces
(the original descriptor, the acceptance relation): the kernel does not reduce
`Std.HashMap`, honestly said — the pass's outputs are measured by compiled `#eval`
(recorded below), its semantics carried by the theorems. -/

instance : Hashable (ZMod 7) := ⟨fun x => hash x.val⟩
instance : Hashable (ZMod 13) := ⟨fun x => hash x.val⟩

/-- The shared-subterm expression `(x+2)·(x+2)` — one subterm, used twice. -/
def exShared : Term (AirSig (ZMod 7) Unit) :=
  mul' (add' (vr ()) (cst 2)) (add' (vr ()) (cst 2))

/-- Its emitted descriptor — layout: `x` at wire 0 (public), aux at offset 1. -/
def exSharedDescriptor : ConstraintDescriptor (ZMod 7) :=
  emit (fun _ : Unit => 0) 1 1 [exShared]

/-- *Computed, literal*: the DUPLICATION is visible — the add gate emitted twice
(`w₀+2 = w₁` and `w₀+2 = w₂`), then `w₁·w₂ = w₃`, root zero-check on `w₃`. -/
example : exSharedDescriptor =
    { nPublic := 1, nVars := 1, nWires := 4,
      gates := [⟨.add, .wire 0, .cnst 2, 1⟩, ⟨.add, .wire 0, .cnst 2, 2⟩,
        ⟨.mul, .wire 1, .wire 2, 3⟩],
      zeros := [.wire 3] } := by decide

/-- The emitted descriptor is SSA — `emit_ssa` fires, no side condition left. -/
example : exSharedDescriptor.SSA :=
  emit_ssa (fun _ : Unit => 0) 1 1 (fun _ => Nat.one_pos) [exShared]

/- *Measured, compiled `#eval` — audit notes, not kernel theorems (the kernel does not
reduce `Std.HashMap`):
`(cse exSharedDescriptor).gates.length = 2` (from 3 — the duplicated add gate MERGED),
`(cse exSharedDescriptor).gates = [⟨.add, .wire 0, .cnst 2, 1⟩, ⟨.mul, .wire 1, .wire 1, 3⟩]`
(the mul now reads the SHARED wire `w₁` twice — `decide`d by compiled `#eval`, `true`),
`(cse exSharedDescriptor).zeros = [.wire 3]` (the root check survives on the kept wire). -/

/-- *Satisfiable, forward, SAME witness*: at `x = 5` the honest vector
`(5, 5+2=0, 0, 0·0=0)` satisfies the ORIGINAL descriptor (decided — kernel-checkable
there), hence the CSE'd one by `cse_holds`. The dropped wire `w₂` keeps its value; the
CSE'd descriptor simply no longer constrains it. -/
example : descriptorHolds (cse exSharedDescriptor)
    (fun n => if n = 0 then 5 else 0) :=
  cse_holds exSharedDescriptor _ (by decide)

/-- *Satisfiable, through the re-closed seam*: at `x = 5`, `(5+2)² = 49 = 0` over
`ZMod 7` — a satisfying vector for the CSE'd descriptor EXISTS, built by the theorem. -/
example : ∃ wv : ℕ → ZMod 7, (∀ i : Unit, wv ((fun _ : Unit => 0) i) = (5 : ZMod 7)) ∧
    descriptorHolds (cse exSharedDescriptor) wv :=
  (cse_emit_accepts_iff (fun _ : Unit => 0) (fun a b _ => Subsingleton.elim a b) 1 1
    (fun _ => Nat.one_pos) (fun _ => (5 : ZMod 7)) [exShared]).mpr (by decide)

/-- *Teeth, strongest form — rejection PRESERVED*: at `x = 3` (where `(3+2)² = 4 ≠ 0`) NO
total wire vector whatsoever satisfies the CSE'd descriptor — the merge did not open a
hole. Backward faithfulness at work: a satisfying vector would pull back to one for the
original, which cannot exist. -/
example : ¬ ∃ wv : ℕ → ZMod 7,
    (∀ i : Unit, wv ((fun _ : Unit => 0) i) = (3 : ZMod 7)) ∧
      descriptorHolds (cse exSharedDescriptor) wv := fun h =>
  (by decide : ¬ systemAccepts (fun _ : Unit => (3 : ZMod 7)) [exShared])
    ((cse_emit_accepts_iff (fun _ : Unit => 0) (fun a b _ => Subsingleton.elim a b) 1 1
      (fun _ => Nat.one_pos) (fun _ => (3 : ZMod 7)) [exShared]).mp h)

/-- *Teeth, specific violating witness*: the vector pinning `x = 3` (with any aux values)
still FAILS the CSE'd descriptor — the corollary of the strongest form. -/
example : ¬ descriptorHolds (cse exSharedDescriptor)
    (fun n => if n = 0 then 3 else 0) := fun h =>
  (by decide : ¬ systemAccepts (fun _ : Unit => (3 : ZMod 7)) [exShared])
    ((cse_emit_accepts_iff (fun _ : Unit => 0) (fun a b _ => Subsingleton.elim a b) 1 1
      (fun _ => Nat.one_pos) (fun _ => (3 : ZMod 7)) [exShared]).mp
      ⟨_, fun _ => rfl, h⟩)

/-! ## §9. The worked example — the note-spend descriptor, SHARED (`ZMod 13`).

`spendDescriptor` (REUSED verbatim from `Emit` §8) at the same `Fin 11` layout. -/

/-- **The note-spend descriptor, CSE'd** — the deployed object of this rung. -/
def spendDescriptorShared : ConstraintDescriptor (ZMod 13) := cse spendDescriptor

/- *Measured, compiled `#eval` — audit notes, not kernel theorems:
`spendDescriptor.gates.length = 2696666` (`Emit` §8's tree blowup), and
`spendDescriptorShared.gates.length = 220` — the CSE recovers the DAG, a ≈12,258×
gate-count reduction (the demo spend's true DAG is 220 nodes; the tree-flatten duplicated
it exponentially — the membership mux re-reading the hash state, the S-box chains
re-reading their bases, exactly as `[EMIT-share]` diagnosed); `zeros.length = 8`
(unchanged — one root per term), `nWires = 2696677` (unchanged, the wire NUMBERING is
kept — `[EMIT-share-compact]`). -/

/-- The spend descriptor is SSA — the backward direction applies to the deployed object. -/
example : spendDescriptor.SSA := emit_ssa Fin.val 2 11 (fun i => i.isLt) spendSystem

set_option maxRecDepth 2048 in
/-- *Satisfiable*: the honest demo spend yields a total wire vector satisfying the CSE'd
note-spend descriptor — the re-closed seam + `noteSpend_correct` (REUSED), acceptance
decided against the real fold. -/
example : ∃ wv : ℕ → ZMod 13, (∀ i : Fin 11, wv i.val = spendVals i) ∧
    descriptorHolds spendDescriptorShared wv := by
  refine (cse_emit_accepts_iff_fin 11 2 spendVals spendSystem).mpr ?_
  show systemAccepts spendVals (noteSpendSystem _ _ _ _ _ _ _ _ _ _)
  rw [noteSpend_correct]
  decide

/-- *Teeth*: under a WRONG nullifier (`5 ≠ 4 = H_nf(3,8)`) NO total wire vector satisfies
the CSE'd descriptor — merging 2.7M gates down to thousands did not loosen the binding of
the nullifier to the note. -/
example : ¬ ∃ wv : ℕ → ZMod 13,
    (∀ i : Fin 11, wv i.val = (![5, 11, 3, 8, 1, 1, 7, 4, 7, 1, 0] : Fin 11 → ZMod 13) i) ∧
      descriptorHolds spendDescriptorShared wv := fun h => by
  have hacc := (cse_emit_accepts_iff_fin 11 2 _ spendSystem).mp h
  rw [show spendSystem = noteSpendSystem demoNfSpec demoSpec demoSpec
      (fun i : Fin 2 => (⟨2 + i.val, by have := i.isLt; omega⟩ : Fin 11)) 0
      (fun i : Fin 2 => (⟨4 + i.val, by have := i.isLt; omega⟩ : Fin 11))
      0 6 1 [(7, 9), (8, 10)] from rfl, noteSpend_correct] at hacc
  revert hacc
  decide

end Minidregg.Compiler
