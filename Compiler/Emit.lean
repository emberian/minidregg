/-
# `Compiler/Emit.lean` — the EMIT PATH: the gate system serialized to a prover-consumable
descriptor, FAITHFULLY

**Substrate, said out loud: the emit path is Lean-AUTHORED and its faithfulness is a THEOREM
over the actual emitted object.** Native code has no semantics to refine and does not consume
this descriptor today. It may only compute candidate buffers behind a Lean-owned plan; Lean
checks those buffers against the emitted `ConstraintDescriptor` before constructing any
accepted token.

## The construction

* `ConstraintDescriptor` — a FIRST-ORDER, serializable gate-system representation: a list of
  gate records (`op ∈ {add, mul}`, input wires by index-or-constant, output wire by index), a
  list of zero-checked wires (the boundary constraints — each flattened term's root pinned to
  `0`), the total wire count, and the public/witness split. Plain data — `ℕ`s, field
  constants, lists; NO functions inside (N3-clean), `DecidableEq` derived. Wire layout: the
  original variables occupy `[0, nVars)` (`[0, nPublic)` of them public), the flattener's aux
  wires sit at offset `nVars`.
* `emit` — the serialization: `flattenSystem` threads `AirFlatten`'s `flatten` (REUSED, the
  fold — never re-derived) over the constraint system's terms with a monotone fresh counter,
  and `emit` maps the resulting gates/roots through the wire layout. A fold and a map —
  nothing else.
* `descriptorHolds : ConstraintDescriptor F → (ℕ → F) → Prop` — the descriptor's OWN
  satisfaction relation, reading gates purely by index into one total wire vector. It never
  mentions `Term`, `flatten`, or another compiler function. This relation remains in Lean;
  native code may suggest a wire vector but cannot establish or decide it.

## The faithfulness (what is PROVED, and in which direction)

* `emit_faithful` — **the keystone**: for EVERY total wire vector `wv`,
  `descriptorHolds (emit ix nPublic nVars s) wv` IFF the readback of `wv` through the layout
  (variables at their indices, aux at offset) satisfies the Lean gate system —
  `gatesHold` on the flattened gates PLUS every root wire reading `0`. Unconditional, both
  directions, no hypotheses: checking the descriptor IS checking the Lean AIR.
* `emit_accepts_iff` — the seam closed existentially: for an injective in-range layout, SOME
  total wire vector pinning the variable wires to `asg` satisfies the emitted descriptor IFF
  `systemAccepts asg s` — chained through `flattenSystem_forces` (wire-forcing, reused from
  `flatten_forces`) and `flattenSystem_sound` (the forced extensions of each term, merged
  along `flatten_scoped`'s non-collision). With `systemAccepts_iff_systemSemHolds` this
  reaches the EXECUTOR relation: the descriptor means what the semantics say, end to end.
* `emit_wellFormed` — every emitted wire index is `< nWires`, gate outputs land in the aux
  region `[nVars, nWires)`: the prover can size its buffers from the descriptor header alone.

## Residuals (named, none stubbed)

* `[EMIT-backend]` — a Lean-emitted online plan that requests bounded native computation,
  validates every returned buffer against this descriptor, and only then advances the
  Lean-owned transcript/controller. The historical Rust descriptor reader and
  BabyBear⁴/FRI/WGPU path were deleted; no current native module consumes this descriptor.
* `[EMIT-sound]` — the deployed claim "the prover ACCEPTED, therefore `descriptorHolds`"
  inherits the FRI/STARK floor (`Loom`'s undischarged soundness residuals plus the backend's
  honest implementation of the IOP). This file proves the descriptor MEANS the Lean AIR; it
  does NOT claim the unverified prover's acceptance implies the descriptor's satisfaction.
  "It proves on a box" stays exactly that until the floor is discharged.
* `[EMIT-share]` — CLOSED in `Compiler/EmitShare`. `flatten` serializes the term TREE:
  duplicated subterms (the membership mux re-reads the hash state, the S-box chains re-read
  their base) emit duplicated gates — the demo note-spend measures 2,696,666 gates (compiled
  `#eval`, §8). Faithfulness is unaffected (every copy is forced to the same value); the
  `cse` pass — a compiler rung with its OWN faithfulness theorem (`cse_faithful`,
  `cse_emit_accepts_iff`), derived like this one, never a hand-tuned emitted list — merges
  the copies; what remains there is `[EMIT-share-compact]` (wire renumbering + dead-gate
  sweep).
-/
import Compiler.AirFlatten
import Compiler.NoteSpend

namespace Minidregg.Compiler

universe u

variable {F : Type u} [Field F] {Idx : Type u}

/-! ## §1. The descriptor — first-order, serializable, prover-consumable. -/

/-- A descriptor wire operand: a literal field constant or a wire INDEX into the one total
wire vector. Plain data — the `Idx`-abstraction and the var/aux distinction are gone,
resolved by the emit layout. -/
inductive DWire (F : Type u)
  | cnst (c : F)
  | wire (n : ℕ)
deriving DecidableEq

/-- A descriptor gate record: `a ⋄ b = out`, `⋄ ∈ {add, mul}` (`GateOp` REUSED from
`AirFlatten`), inputs by constant-or-index, output by index. Degree ≤ 2 by shape, exactly as
the source `Gate`. -/
structure DGate (F : Type u) where
  op : GateOp
  a : DWire F
  b : DWire F
  out : ℕ
deriving DecidableEq

/-- **The constraint descriptor** — what the (unverified) prover consumes. Plain first-order
data: two `ℕ` counts, the split, a gate list, and the zero-checked wires (each flattened
term's root — the boundary constraints). No functions anywhere inside. Layout convention:
wires `[0, nPublic)` are the public inputs, `[0, nVars)` the original variables,
`[nVars, nWires)` the flattener's aux wires. -/
structure ConstraintDescriptor (F : Type u) where
  nPublic : ℕ
  nVars : ℕ
  nWires : ℕ
  gates : List (DGate F)
  zeros : List (DWire F)
deriving DecidableEq

/-- Read a descriptor operand against a total wire vector. -/
def DWire.read (wv : ℕ → F) : DWire F → F
  | .cnst c => c
  | .wire n => wv n

omit [Field F] in
@[simp] theorem DWire.read_cnst (wv : ℕ → F) (c : F) :
    (DWire.cnst c).read wv = c := rfl

omit [Field F] in
@[simp] theorem DWire.read_wire (wv : ℕ → F) (n : ℕ) :
    (DWire.wire n).read wv = wv n := rfl

/-- A descriptor gate holds under a total wire vector. -/
def DGate.holds (wv : ℕ → F) (g : DGate F) : Prop :=
  g.op.denote (g.a.read wv) (g.b.read wv) = wv g.out

/-- **The descriptor's satisfaction relation** — the first-order check the prover
establishes: every gate record holds and every zero-checked wire reads `0`. Reads the
descriptor purely by index; mentions no Lean function, no `Term`, no `flatten`. -/
def descriptorHolds (d : ConstraintDescriptor F) (wv : ℕ → F) : Prop :=
  (∀ g ∈ d.gates, g.holds wv) ∧ (∀ z ∈ d.zeros, z.read wv = 0)

instance [DecidableEq F] (wv : ℕ → F) (g : DGate F) : Decidable (g.holds wv) :=
  inferInstanceAs (Decidable (g.op.denote (g.a.read wv) (g.b.read wv) = wv g.out))

instance [DecidableEq F] (d : ConstraintDescriptor F) (wv : ℕ → F) :
    Decidable (descriptorHolds d wv) :=
  inferInstanceAs (Decidable ((∀ g ∈ d.gates, g.holds wv) ∧ (∀ z ∈ d.zeros, z.read wv = 0)))

/-! ## §2. The serialization — flatten the system (REUSING `flatten`), lay out the wires. -/

/-- Result of flattening a whole constraint system: all gates (in allocation order), each
term's root wire (to be pinned to `0`), and the final fresh counter. -/
structure FlatSystem (F : Type u) (Idx : Type u) where
  gates : List (Gate F Idx)
  roots : List (WireRef F Idx)
  next : ℕ

/-- Flatten every term of a constraint system, threading the fresh counter so no two terms'
aux wires collide. Each recursion step is one call of `AirFlatten.flatten` — the fold,
REUSED, never re-derived. -/
def flattenSystem : ConstraintSystem F Idx → ℕ → FlatSystem F Idx
  | [], n => ⟨[], [], n⟩
  | t :: ts, n =>
      let fo := flatten t n
      let rest := flattenSystem ts fo.next
      ⟨fo.gates ++ rest.gates, fo.out :: rest.roots, rest.next⟩

omit [Field F] in
@[simp] theorem flattenSystem_cons_gates (t : Term (AirSig F Idx))
    (ts : ConstraintSystem F Idx) (n : ℕ) :
    (flattenSystem (t :: ts) n).gates =
      (flatten t n).gates ++ (flattenSystem ts (flatten t n).next).gates := rfl

omit [Field F] in
@[simp] theorem flattenSystem_cons_roots (t : Term (AirSig F Idx))
    (ts : ConstraintSystem F Idx) (n : ℕ) :
    (flattenSystem (t :: ts) n).roots =
      (flatten t n).out :: (flattenSystem ts (flatten t n).next).roots := rfl

omit [Field F] in
@[simp] theorem flattenSystem_cons_next (t : Term (AirSig F Idx))
    (ts : ConstraintSystem F Idx) (n : ℕ) :
    (flattenSystem (t :: ts) n).next = (flattenSystem ts (flatten t n).next).next := rfl

/-- The wire layout: original variable `i` sits at index `ix i`; aux wire `n` at
`nVars + n`; constants stay constants. -/
def emitWire (ix : Idx → ℕ) (nVars : ℕ) : WireRef F Idx → DWire F
  | .cnst c => .cnst c
  | .var i => .wire (ix i)
  | .aux n => .wire (nVars + n)

/-- Serialize one gate through the layout. -/
def emitGate (ix : Idx → ℕ) (nVars : ℕ) (g : Gate F Idx) : DGate F :=
  ⟨g.op, emitWire ix nVars g.a, emitWire ix nVars g.b, nVars + g.out⟩

/-- **The emit** — serialize a constraint system to its prover-consumable descriptor:
flatten (the fold), then map the layout over gates and roots. The zero-checks are the
flattened terms' root wires — the boundary constraints pinning each assertion to `0`. -/
def emit (ix : Idx → ℕ) (nPublic nVars : ℕ) (s : ConstraintSystem F Idx) :
    ConstraintDescriptor F where
  nPublic := nPublic
  nVars := nVars
  nWires := nVars + (flattenSystem s 0).next
  gates := ((flattenSystem s 0).gates).map (emitGate ix nVars)
  zeros := ((flattenSystem s 0).roots).map (emitWire ix nVars)

/-! ## §3. Readback and `emit_faithful` — the descriptor MEANS the gate system. -/

/-- Read the variable assignment a total wire vector induces through the layout. -/
def readVars (ix : Idx → ℕ) (wv : ℕ → F) : Idx → F := fun i => wv (ix i)

/-- Read the aux valuation a total wire vector induces (the region at offset `nVars`). -/
def readAux (nVars : ℕ) (wv : ℕ → F) : ℕ → F := fun n => wv (nVars + n)

omit [Field F] in
/-- A serialized operand reads exactly what its source wire reads under the readback. -/
@[simp] theorem emitWire_read (ix : Idx → ℕ) (nVars : ℕ) (wv : ℕ → F)
    (w : WireRef F Idx) :
    (emitWire ix nVars w).read wv = w.read (readVars ix wv) (readAux nVars wv) := by
  cases w <;> rfl

/-- A serialized gate holds IFF its source gate holds under the readback — the per-gate
faithfulness, definitional after the operand reads. -/
theorem emitGate_holds_iff (ix : Idx → ℕ) (nVars : ℕ) (wv : ℕ → F) (g : Gate F Idx) :
    (emitGate ix nVars g).holds wv ↔
      g.holds (readVars ix wv) (readAux nVars wv) := by
  show g.op.denote ((emitWire ix nVars g.a).read wv) ((emitWire ix nVars g.b).read wv)
        = wv (nVars + g.out)
      ↔ g.op.denote (g.a.read (readVars ix wv) (readAux nVars wv))
          (g.b.read (readVars ix wv) (readAux nVars wv))
        = readAux nVars wv g.out
  rw [emitWire_read, emitWire_read]
  exact Iff.rfl

/-- **`emit_faithful` — the emit-path keystone.** For EVERY total wire vector, satisfying the
emitted descriptor is EXACTLY satisfying the Lean gate system under the readback: all
flattened gates hold (`gatesHold`, `AirFlatten`'s relation, REUSED) and every term's root
wire reads `0`. Unconditional — no injectivity, no bounds, both directions: the descriptor's
first-order semantics and the compiler's proved semantics are the same relation. The prover
checks the descriptor; this theorem says that IS checking the Lean AIR. -/
theorem emit_faithful (ix : Idx → ℕ) (nPublic nVars : ℕ) (s : ConstraintSystem F Idx)
    (wv : ℕ → F) :
    descriptorHolds (emit ix nPublic nVars s) wv ↔
      (gatesHold (readVars ix wv) (readAux nVars wv) (flattenSystem s 0).gates ∧
        ∀ r ∈ (flattenSystem s 0).roots,
          r.read (readVars ix wv) (readAux nVars wv) = 0) := by
  unfold descriptorHolds gatesHold
  apply and_congr
  · show (∀ g ∈ ((flattenSystem s 0).gates).map (emitGate ix nVars), g.holds wv) ↔ _
    rw [List.forall_mem_map]
    exact forall₂_congr fun g _ => emitGate_holds_iff ix nVars wv g
  · show (∀ z ∈ ((flattenSystem s 0).roots).map (emitWire ix nVars), z.read wv = 0) ↔ _
    rw [List.forall_mem_map]
    exact forall₂_congr fun r _ => by rw [emitWire_read]

/-! ## §4. The system-level flatten semantics — forcing, soundness, scoping (all REUSED from
`AirFlatten`'s per-term theorems, lifted along the list). -/

omit [Field F] in
/-- System-level freshness: the counter is monotone, every root and every gate of the
flattened system is scoped inside the allocated range `[n₀, next)`. Lifted from
`flatten_scoped` by one list induction. -/
theorem flattenSystem_scoped (s : ConstraintSystem F Idx) (n₀ : ℕ) :
    n₀ ≤ (flattenSystem s n₀).next ∧
      (∀ r ∈ (flattenSystem s n₀).roots, r.auxIn n₀ (flattenSystem s n₀).next) ∧
      ∀ g ∈ (flattenSystem s n₀).gates, g.scopedIn n₀ (flattenSystem s n₀).next := by
  induction s generalizing n₀ with
  | nil =>
    refine ⟨le_rfl, ?_, ?_⟩
    · intro r hr
      exact nomatch hr
    · intro g hg
      exact nomatch hg
  | cons t ts ih =>
    obtain ⟨hle₁, hout, hgl⟩ := flatten_scoped t n₀
    obtain ⟨hle₂, hroots, hgr⟩ := ih (flatten t n₀).next
    refine ⟨hle₁.trans hle₂, ?_, ?_⟩
    · rw [flattenSystem_cons_roots]
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact WireRef.auxIn_mono le_rfl hle₂ hout
      · exact WireRef.auxIn_mono hle₁ le_rfl (hroots r hr')
    · rw [flattenSystem_cons_gates]
      intro g hg
      rcases List.mem_append.mp hg with hg' | hg'
      · exact Gate.scopedIn_mono le_rfl hle₂ (hgl g hg')
      · exact Gate.scopedIn_mono hle₁ le_rfl (hgr g hg')

/-- **System-level wire-forcing (the sound direction)**: ANY aux valuation satisfying every
flattened gate with every root reading `0` witnesses `systemAccepts` — each term's root is
forced to its `eval` (`flatten_forces`, REUSED), and the zero-check finishes it. -/
theorem flattenSystem_forces (asg : Idx → F) (auxv : ℕ → F) (s : ConstraintSystem F Idx)
    (n₀ : ℕ) (hg : gatesHold asg auxv (flattenSystem s n₀).gates)
    (hr : ∀ r ∈ (flattenSystem s n₀).roots, r.read asg auxv = 0) :
    systemAccepts asg s := by
  induction s generalizing n₀ with
  | nil => intro t ht; exact nomatch ht
  | cons t ts ih =>
    rw [flattenSystem_cons_gates] at hg
    rw [flattenSystem_cons_roots] at hr
    have hgt : gatesHold asg auxv (flatten t n₀).gates := fun g hgm =>
      hg g (List.mem_append_left _ hgm)
    have hgts : gatesHold asg auxv (flattenSystem ts (flatten t n₀).next).gates :=
      fun g hgm => hg g (List.mem_append_right _ hgm)
    have hrts : ∀ r ∈ (flattenSystem ts (flatten t n₀).next).roots, r.read asg auxv = 0 :=
      fun r hrm => hr r (List.mem_cons_of_mem _ hrm)
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu'
    · show eval asg u = 0
      rw [← flatten_forces asg u n₀ auxv hgt]
      exact hr _ (List.mem_cons_self ..)
    · exact ih (flatten t n₀).next hgts hrts u hu'

/-- **System-level soundness (completeness)**: an accepted system HAS a satisfying aux
valuation with every root reading `0` — each term's forced extension (`flatten_sound`,
REUSED) merged along the non-colliding ranges (`flatten_scoped` / `flattenSystem_scoped`). -/
theorem flattenSystem_sound (asg : Idx → F) (s : ConstraintSystem F Idx) (n₀ : ℕ)
    (hacc : systemAccepts asg s) :
    ∃ auxv : ℕ → F, gatesHold asg auxv (flattenSystem s n₀).gates ∧
      ∀ r ∈ (flattenSystem s n₀).roots, r.read asg auxv = 0 := by
  induction s generalizing n₀ with
  | nil =>
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro g hg
      exact nomatch hg
    · intro r hr
      exact nomatch hr
  | cons t ts ih =>
    have hat : accepts asg t := hacc t (List.mem_cons_self ..)
    have hats : systemAccepts asg ts := fun u hu => hacc u (List.mem_cons_of_mem _ hu)
    obtain ⟨auxv₁, hg₁, ho₁⟩ := flatten_sound asg t n₀
    obtain ⟨auxv₂, hg₂, hr₂⟩ := ih (flatten t n₀).next hats
    obtain ⟨hle₁, hout, hsl⟩ := flatten_scoped t n₀
    obtain ⟨hle₂, hroots, hsr⟩ := flattenSystem_scoped ts (flatten t n₀).next
    refine ⟨fun m => if m < (flatten t n₀).next then auxv₁ m else auxv₂ m, ?_, ?_⟩
    · rw [flattenSystem_cons_gates]
      have hA1 : ∀ m, n₀ ≤ m → m < (flatten t n₀).next → auxv₁ m =
          (fun m => if m < (flatten t n₀).next then auxv₁ m else auxv₂ m) m :=
        fun m _ hm => (if_pos hm).symm
      have hA2 : ∀ m, (flatten t n₀).next ≤ m →
          m < (flattenSystem ts (flatten t n₀).next).next → auxv₂ m =
          (fun m => if m < (flatten t n₀).next then auxv₁ m else auxv₂ m) m :=
        fun m hm _ => (if_neg (by omega)).symm
      intro g hg
      rcases List.mem_append.mp hg with hgm | hgm
      · exact Gate.holds_congr hA1 (hsl g hgm) (hg₁ g hgm)
      · exact Gate.holds_congr hA2 (hsr g hgm) (hg₂ g hgm)
    · rw [flattenSystem_cons_roots]
      have hA1 : ∀ m, n₀ ≤ m → m < (flatten t n₀).next → auxv₁ m =
          (fun m => if m < (flatten t n₀).next then auxv₁ m else auxv₂ m) m :=
        fun m _ hm => (if_pos hm).symm
      have hA2 : ∀ m, (flatten t n₀).next ≤ m →
          m < (flattenSystem ts (flatten t n₀).next).next → auxv₂ m =
          (fun m => if m < (flatten t n₀).next then auxv₁ m else auxv₂ m) m :=
        fun m hm _ => (if_neg (by omega)).symm
      intro r hrm
      rcases List.mem_cons.mp hrm with rfl | hrm'
      · rw [← WireRef.read_congr hA1 hout, ho₁]
        exact hat
      · rw [← WireRef.read_congr hA2 (hroots r hrm')]
        exact hr₂ r hrm'

/-! ## §5. The seam, closed existentially — descriptor satisfiability IS system acceptance. -/

/-- **`emit_accepts_iff` — the emit path end to end.** For an injective, in-range wire
layout: SOME total wire vector pinning the variable wires to `asg` satisfies the emitted
descriptor IFF the constraint system accepts `asg`. Forward by readback + system-level
wire-forcing; backward by building the vector from `asg` and the merged forced extension.
The prover's satisfying witness and the compiler's accepting assignment are the same
object, seen from the two sides of the seam. -/
theorem emit_accepts_iff (ix : Idx → ℕ) (hinj : Function.Injective ix)
    (nPublic nVars : ℕ) (hbound : ∀ i, ix i < nVars)
    (asg : Idx → F) (s : ConstraintSystem F Idx) :
    (∃ wv : ℕ → F, (∀ i, wv (ix i) = asg i) ∧
        descriptorHolds (emit ix nPublic nVars s) wv)
      ↔ systemAccepts asg s := by
  constructor
  · rintro ⟨wv, hpin, hd⟩
    rw [emit_faithful] at hd
    rw [show readVars ix wv = asg from funext hpin] at hd
    exact flattenSystem_forces asg (readAux nVars wv) s 0 hd.1 hd.2
  · intro hacc
    classical
    obtain ⟨auxv, hg, hr⟩ := flattenSystem_sound asg s 0 hacc
    refine ⟨fun n => if h : ∃ i, ix i = n then asg h.choose
        else if n < nVars then 0 else auxv (n - nVars), fun i => ?_, ?_⟩
    · have hex : ∃ j, ix j = ix i := ⟨i, rfl⟩
      simp only [dif_pos hex]
      exact congrArg asg (hinj hex.choose_spec)
    · rw [emit_faithful]
      have hrv : readVars ix (fun n => if h : ∃ i, ix i = n then asg h.choose
          else if n < nVars then 0 else auxv (n - nVars)) = asg := funext fun i => by
        have hex : ∃ j, ix j = ix i := ⟨i, rfl⟩
        simp only [readVars, dif_pos hex]
        exact congrArg asg (hinj hex.choose_spec)
      have hra : readAux nVars (fun n => if h : ∃ i, ix i = n then asg h.choose
          else if n < nVars then 0 else auxv (n - nVars)) = auxv := funext fun n => by
        have hnex : ¬ ∃ i, ix i = nVars + n := by
          rintro ⟨i, hi⟩
          have := hbound i
          omega
        simp only [readAux, dif_neg hnex, if_neg (by omega : ¬ nVars + n < nVars)]
        rw [Nat.add_sub_cancel_left]
      rw [hrv, hra]
      exact ⟨hg, hr⟩

/-- The seam at the canonical `Fin m` layout: variable `i` at wire `i`, aux at offset `m`.
Stated over a `Type`-level field (`Fin` lives in `Type 0`); the general layout form is
`emit_accepts_iff`. -/
theorem emit_accepts_iff_fin {K : Type} [Field K] (m nPublic : ℕ) (asg : Fin m → K)
    (s : ConstraintSystem K (Fin m)) :
    (∃ wv : ℕ → K, (∀ i : Fin m, wv i.val = asg i) ∧
        descriptorHolds (emit Fin.val nPublic m s) wv)
      ↔ systemAccepts asg s :=
  emit_accepts_iff Fin.val Fin.val_injective nPublic m (fun i => i.isLt) asg s

/-- The seam reaches the EXECUTOR relation: descriptor satisfiability is `systemSemHolds` —
`emit_accepts_iff` chained through rung 1's initiality transfer. The descriptor means what
the independent hand-recursed semantics say, with the whole compiler chain in between. -/
theorem emit_semHolds_iff (ix : Idx → ℕ) (hinj : Function.Injective ix)
    (nPublic nVars : ℕ) (hbound : ∀ i, ix i < nVars)
    (asg : Idx → F) (s : ConstraintSystem F Idx) :
    (∃ wv : ℕ → F, (∀ i, wv (ix i) = asg i) ∧
        descriptorHolds (emit ix nPublic nVars s) wv)
      ↔ systemSemHolds asg s := by
  rw [emit_accepts_iff ix hinj nPublic nVars hbound asg s,
    systemAccepts_iff_systemSemHolds]

/-! ## §6. Well-formedness — the prover can size its buffers from the header. -/

/-- A descriptor operand is bounded: any wire index it carries is `< n`. -/
def DWire.bounded (n : ℕ) : DWire F → Prop
  | .cnst _ => True
  | .wire m => m < n

/-- A well-formed descriptor: the split is nested (`nPublic ≤ nVars ≤ nWires`), every gate
operand and zero-check indexes below `nWires`, and every gate OUTPUT lands in the aux region
`[nVars, nWires)` — gates only ever define aux wires, never overwrite inputs. -/
structure ConstraintDescriptor.WellFormed (d : ConstraintDescriptor F) : Prop where
  public_le : d.nPublic ≤ d.nVars
  vars_le : d.nVars ≤ d.nWires
  gates_in : ∀ g ∈ d.gates, g.a.bounded d.nWires ∧ g.b.bounded d.nWires ∧
    d.nVars ≤ g.out ∧ g.out < d.nWires
  zeros_in : ∀ z ∈ d.zeros, z.bounded d.nWires

omit [Field F] in
/-- A scoped source wire serializes to a bounded operand. -/
theorem emitWire_bounded (ix : Idx → ℕ) {nVars N lo hi : ℕ} (hbound : ∀ i, ix i < nVars)
    (hN : nVars + hi ≤ N) {w : WireRef F Idx} (hw : w.auxIn lo hi) :
    (emitWire ix nVars w).bounded N := by
  cases w with
  | cnst c => trivial
  | var i => show ix i < N; have := hbound i; omega
  | aux n => show nVars + n < N; have := hw.2; omega

omit [Field F] in
/-- **The emitted descriptor is well-formed** (in-range layout): all indices below `nWires`,
all gate outputs in the aux region — from `flattenSystem_scoped`, nothing else. -/
theorem emit_wellFormed (ix : Idx → ℕ) (nPublic nVars : ℕ) (hpub : nPublic ≤ nVars)
    (hbound : ∀ i, ix i < nVars) (s : ConstraintSystem F Idx) :
    (emit ix nPublic nVars s).WellFormed := by
  obtain ⟨-, hroots, hgates⟩ := flattenSystem_scoped s 0
  refine ⟨hpub, Nat.le_add_right _ _, ?_, ?_⟩
  · intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
    obtain ⟨ha, hb, -, hhi⟩ := hgates g₀ hg₀
    exact ⟨emitWire_bounded ix hbound
        (by show nVars + g₀.out ≤ nVars + (flattenSystem s 0).next; omega) ha,
      emitWire_bounded ix hbound
        (by show nVars + g₀.out ≤ nVars + (flattenSystem s 0).next; omega) hb,
      Nat.le_add_right _ _,
      by show nVars + g₀.out < nVars + (flattenSystem s 0).next; omega⟩
  · intro z hz
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
    exact emitWire_bounded ix hbound le_rfl (hroots r hr)

/-! ## §7. Keystone witnesses, BUILT — `ZMod 7`, `AirFlatten`'s example expression.

`exFlat = (x + 2)·x` (REUSED), the one-term system `[exFlat]`, layout `x ↦ wire 0`,
`nVars = 1`. The emitted descriptor is exhibited LITERALLY — the audit that it is genuinely
first-order data. -/

/-- The emitted descriptor of the example system — layout: `x` at wire 0 (public), aux at
offset 1. -/
def exDescriptor : ConstraintDescriptor (ZMod 7) :=
  emit (fun _ : Unit => 0) 1 1 [exFlat]

/-- *Computed, literal*: the descriptor is plain data — 3 wires (`x`, `aux₀`, `aux₁`), the
two serialized gates `w₀ + 2 = w₁` and `w₁ · w₀ = w₂`, one zero-check on the root `w₂`. -/
example : exDescriptor =
    { nPublic := 1, nVars := 1, nWires := 3,
      gates := [⟨.add, .wire 0, .cnst 2, 1⟩, ⟨.mul, .wire 1, .wire 0, 2⟩],
      zeros := [.wire 2] } := by decide

/-- *Satisfiable, decided on the descriptor's OWN relation*: at `x = 5` the honest total
wire vector `(5, 5+2=0, 0·5=0)` satisfies `descriptorHolds` — computed by the first-order
check alone, no Lean-side semantics consulted. -/
example : descriptorHolds exDescriptor (fun n => if n = 0 then 5 else 0) := by decide

/-- *Teeth (gate), decided*: tampering the aux wire (`w₁ ↦ 3` instead of the forced `0`)
violates the descriptor — the gate records genuinely constrain. -/
example : ¬ descriptorHolds exDescriptor
    (fun n => if n = 0 then 5 else if n = 1 then 3 else 0) := by decide

/-- *Teeth (zero-check), decided*: at `x = 3` the FORCED wire vector `(3, 5, 1)` satisfies
every gate record yet fails the descriptor — the root zero-check alone rejects it. Both
components of `descriptorHolds` bite. -/
example : (∀ g ∈ exDescriptor.gates,
      g.holds (fun n => if n = 0 then 3 else if n = 1 then 5 else 1)) ∧
    ¬ descriptorHolds exDescriptor
      (fun n => if n = 0 then 3 else if n = 1 then 5 else 1) := by
  refine ⟨by decide, by decide⟩

/-- *Faithfulness FIRES on the example*: for every total wire vector, the descriptor's
satisfaction IS the Lean gate system's — `emit_faithful` instantiated, no `decide`. -/
example (wv : ℕ → ZMod 7) :
    descriptorHolds exDescriptor wv ↔
      (gatesHold (readVars (fun _ : Unit => 0) wv) (readAux 1 wv)
          (flattenSystem [exFlat] 0).gates ∧
        ∀ r ∈ (flattenSystem [exFlat] 0).roots,
          r.read (readVars (fun _ : Unit => 0) wv) (readAux 1 wv) = 0) :=
  emit_faithful (fun _ : Unit => 0) 1 1 [exFlat] wv

/-- *The seam fires, accepting side*: at `x = 5` (where `(5+2)·5 = 0` over `ZMod 7`) a
satisfying total wire vector EXISTS — via `emit_accepts_iff`, the witness built by the
theorem, not by hand. -/
example : ∃ wv : ℕ → ZMod 7, (∀ i : Unit, wv ((fun _ : Unit => 0) i) = (5 : ZMod 7)) ∧
    descriptorHolds (emit (fun _ : Unit => 0) 1 1 [exFlat]) wv :=
  (emit_accepts_iff (fun _ : Unit => 0) (fun a b _ => Subsingleton.elim a b) 1 1
    (fun _ => Nat.one_pos) (fun _ => (5 : ZMod 7)) [exFlat]).mpr (by decide)

/-- *The seam's teeth, strongest form*: at `x = 3` (where the expression evals to `1 ≠ 0`)
NO total wire vector whatsoever — any aux values, any junk wires — satisfies the emitted
descriptor. The prover cannot satisfy the descriptor of an unsatisfiable statement. -/
example : ¬ ∃ wv : ℕ → ZMod 7, (∀ i : Unit, wv ((fun _ : Unit => 0) i) = (3 : ZMod 7)) ∧
    descriptorHolds (emit (fun _ : Unit => 0) 1 1 [exFlat]) wv := fun h =>
  (by decide : ¬ systemAccepts (fun _ : Unit => (3 : ZMod 7)) [exFlat])
    ((emit_accepts_iff (fun _ : Unit => 0) (fun a b _ => Subsingleton.elim a b) 1 1
      (fun _ => Nat.one_pos) (fun _ => (3 : ZMod 7)) [exFlat]).mp h)

/-! ## §8. The worked example — the note-spend EMITTED (`ZMod 13`, the demo specs).

The real target: `noteSpendSystem` (REUSED verbatim from `NoteSpend`) at the canonical
`Fin 11` wire layout — nullifier `w₀` and root `w₁` PUBLIC (`nPublic = 2`), note `w₂ w₃`,
bits `w₄ w₅`, commitment `w₆`, siblings `w₇ w₈`, directions `w₉ w₁₀`. -/

/-- The demo note-spend system on the `Fin 11` layout (specs and demo values from
`NoteSpend`: note `(3,8)`, `w = 2`, `k = 2`, depth 2). -/
def spendSystem : ConstraintSystem (ZMod 13) (Fin 11) :=
  noteSpendSystem demoNfSpec demoSpec demoSpec
    (fun i : Fin 2 => (⟨2 + i.val, by have := i.isLt; omega⟩ : Fin 11)) 0
    (fun i : Fin 2 => (⟨4 + i.val, by have := i.isLt; omega⟩ : Fin 11))
    0 6 1 [(7, 9), (8, 10)]

/-- **The note-spend, emitted** — the concrete prover-consumable descriptor of the shielded
spend at the demo parameters. -/
def spendDescriptor : ConstraintDescriptor (ZMod 13) :=
  emit Fin.val 2 11 spendSystem

/- *Measured, compiled `#eval` — audit notes, not kernel theorems (the flatten of the full
spend is too large for kernel reduction, honestly said):
`spendDescriptor.gates.length = 2696666`, `nWires = 2696677` (= 11 vars + 2696666 aux, one
per gate — `flatten_covers`' no-dangling-allocations, visible in the arithmetic),
`zeros.length = 8` (one root per term: 2 bit-booleanities + recomposition + 2 hashes +
2 direction-booleanities + the root equation), `nPublic = 2`, `nVars = 11`. The gate count
is the TREE-flattening blowup — duplicated subterms emit duplicated gates, `[EMIT-share]`. -/

/-- The demo spend on the wire layout: nullifier `4`, root `11`, note `(3,8)`, bits `(1,1)`,
commitment `7`, siblings `(4,7)`, directions `(1,0)`. -/
def spendVals : Fin 11 → ZMod 13 := ![4, 11, 3, 8, 1, 1, 7, 4, 7, 1, 0]

/-- *Faithfulness fires on the emitted note-spend*: `descriptorHolds (emit noteSpend…)` IS
`gatesHold` + root-zeros on the flattened note-spend, for every total wire vector —
`emit_faithful` instantiated at the real object. -/
example (wv : ℕ → ZMod 13) :
    descriptorHolds spendDescriptor wv ↔
      (gatesHold (readVars Fin.val wv) (readAux 11 wv) (flattenSystem spendSystem 0).gates ∧
        ∀ r ∈ (flattenSystem spendSystem 0).roots,
          r.read (readVars Fin.val wv) (readAux 11 wv) = 0) :=
  emit_faithful Fin.val 2 11 spendSystem wv

set_option maxRecDepth 2048 in
/-- *Satisfiable*: the honest demo spend yields a total wire vector satisfying the emitted
note-spend descriptor — `emit_accepts_iff` + `noteSpend_correct` (REUSED), the acceptance
decided against the real fold. -/
example : ∃ wv : ℕ → ZMod 13, (∀ i : Fin 11, wv i.val = spendVals i) ∧
    descriptorHolds spendDescriptor wv := by
  refine (emit_accepts_iff_fin 11 2 spendVals spendSystem).mpr ?_
  show systemAccepts spendVals (noteSpendSystem _ _ _ _ _ _ _ _ _ _)
  rw [noteSpend_correct]
  decide

/-- *Teeth*: under a WRONG nullifier (`5 ≠ 4 = H_nf(3,8)`) NO total wire vector satisfies
the emitted descriptor — the serialized note-spend still binds the nullifier to the note. -/
example : ¬ ∃ wv : ℕ → ZMod 13,
    (∀ i : Fin 11, wv i.val = (![5, 11, 3, 8, 1, 1, 7, 4, 7, 1, 0] : Fin 11 → ZMod 13) i) ∧
      descriptorHolds spendDescriptor wv := fun h => by
  have hacc := (emit_accepts_iff_fin 11 2 _ spendSystem).mp h
  rw [show spendSystem = noteSpendSystem demoNfSpec demoSpec demoSpec
      (fun i : Fin 2 => (⟨2 + i.val, by have := i.isLt; omega⟩ : Fin 11)) 0
      (fun i : Fin 2 => (⟨4 + i.val, by have := i.isLt; omega⟩ : Fin 11))
      0 6 1 [(7, 9), (8, 10)] from rfl, noteSpend_correct] at hacc
  revert hacc
  decide

/-- *The emitted note-spend descriptor is well-formed* — buffer sizes readable off the
header. -/
example : spendDescriptor.WellFormed :=
  emit_wellFormed Fin.val 2 11 (by omega) (fun i => i.isLt) spendSystem

end Minidregg.Compiler
