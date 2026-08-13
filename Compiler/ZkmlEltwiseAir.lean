/-
# `Compiler/ZkmlEltwiseAir.lean` — ONE zkML op, all the way down

**Substrate, said out loud: this is Lean-authored arithmetization.** The catgrad
fork is a stager — it records ops, shapes and wire ids and authors no constraint.
Every gate below comes out of `Compiler/Air`'s DSL through the proved `emit`; none
is hand-written, and none is written in Rust.

## What this file is

The design memo's cards Z1–Z3 describe a vocabulary, a constraint semantics and an
emitted descriptor. Having that path exist for **one** op is worth more than twenty
ops with no path, so this is one op — elementwise `add` — taken from
`Theory/ZkmlTensorOps.lean`'s denotation to a `ConstraintDescriptor` over BabyBear,
with the meaning preserved at every step by a theorem rather than by inspection.

```
  TOp.bin .add            (Theory: the op, candidate-independent)
    ⇣  denotation                     run S (eltAddTrace t)
  eltAddSystem            (here: the constraint relation, one assertion per element)
    ⇣  eltAddSystem_denotes           systemAccepts ⟺ the denotation holds
  emit                    (Compiler/Emit: the descriptor, emit_faithful)
    ⇣  emit_accepts_iff_fin
  addDemoDescriptor       ⟹ addDemoDescriptor_means_denotation
```

`addDemoDescriptor_means_denotation` is the whole point: **a total wire vector
satisfying the emitted descriptor exists if and only if the vocabulary's denotation
of the trace equals the claimed output.** No step in that chain is an audit.

## What it is NOT

* Not a proof of anything about the *prover*. `[EMIT-sound]` is unchanged: "the
  prover accepted, therefore `descriptorHolds`" still inherits the FRI/STARK floor.
  This file says what the descriptor MEANS.
* Not the matmul. Elementwise `add` is the cheapest op in the vocabulary and it is
  deliberately the one taken first; `notes/zkml-build-log.md` §4 records exactly
  what matmul needs that this does not, and it is not a bigger version of this.
* The generic half (`eltAddSystem`, `eltAddSystem_accepts_iff`,
  `eltAddSystem_denotes`) is proved at an ARBITRARY shape, an arbitrary wire
  layout, an arbitrary field, and an arbitrary ring-shaped scalar reading. Only the
  demo descriptor is concrete.
-/
import Compiler.EmitSerialize
import Theory.ZkmlTensorOps

namespace Minidregg.Compiler

open Minidregg.Theory.ZkmlTensorOps

/-! ## §1. The constraint relation of an elementwise binary op — DERIVED, at any shape.

An elementwise op is one assertion per output element. The emitter therefore needs
the element enumeration `idxList`, and `mem_idxList` is what makes "one assertion
per element of `idxList`" mean "every element is constrained" — an emitter that
dropped an index would constrain a proper subset and nothing downstream would
notice. -/

/-- Where an elementwise op's two operands and its output live in the flat variable
vector. The layout is a parameter: nothing below assumes a particular packing, and
in particular nothing assumes the three regions are disjoint (they need not be — an
in-place op is a legal layout). -/
structure EltLayout (t : TyT) (W : Type) where
  /-- wire carrying element `i` of the first operand -/
  aw : Idx t.shape → W
  /-- wire carrying element `i` of the second operand -/
  bw : Idx t.shape → W
  /-- wire carrying element `i` of the output -/
  ow : Idx t.shape → W

/-- The DSL term asserting ONE output element of an elementwise `add`:
`out − (a + b) ≐ 0`. Built from `Compiler/Air`'s constructors — this is the only
place a gate shape is chosen, and it is chosen once for every shape and layout. -/
def eltAddTerm {F : Type} [Field F] {W : Type} (t : TyT) (L : EltLayout t W)
    (i : Idx t.shape) : Term (AirSig F W) :=
  add' (vr (L.ow i)) (mul' (cst (-1)) (add' (vr (L.aw i)) (vr (L.bw i))))

/-- **The constraint system of an elementwise `add`**, at any shape and layout: one
assertion per element of the row-major enumeration. -/
def eltAddSystem {F : Type} [Field F] {W : Type} (t : TyT) (L : EltLayout t W) :
    ConstraintSystem F W :=
  (idxList t.shape).map (eltAddTerm t L)

/-- The system has exactly one assertion per output element — the emitted size is
the type's element count, not an accident of how the term was written. -/
theorem eltAddSystem_length {F : Type} [Field F] {W : Type} (t : TyT)
    (L : EltLayout t W) : (eltAddSystem (F := F) t L).length = size t.shape := by
  simp [eltAddSystem, length_idxList]

/-- The circuit reading of the system, unpacked: acceptance is exactly the
elementwise equations. -/
theorem eltAddSystem_accepts_iff {F : Type} [Field F] {W : Type} (t : TyT)
    (L : EltLayout t W) (asg : W → F) :
    systemAccepts asg (eltAddSystem t L) ↔
      ∀ i : Idx t.shape, asg (L.ow i) = asg (L.aw i) + asg (L.bw i) := by
  constructor
  · intro hacc i
    have hmem : eltAddTerm (F := F) t L i ∈ eltAddSystem (F := F) t L :=
      List.mem_map.mpr ⟨i, mem_idxList i, rfl⟩
    have h : asg (L.ow i) + (-1) * (asg (L.aw i) + asg (L.bw i)) = 0 := hacc _ hmem
    rw [neg_one_mul, ← sub_eq_add_neg, sub_eq_zero] at h
    exact h
  · intro h u hu
    simp only [eltAddSystem, List.mem_map] at hu
    obtain ⟨i, -, rfl⟩ := hu
    show asg (L.ow i) + (-1) * (asg (L.aw i) + asg (L.bw i)) = 0
    rw [h i]; ring

/-! ## §2. The bridge to the vocabulary — the system MEANS the denotation. -/

/-- The vocabulary op this system is the constraint relation *of*: elementwise `add`
over a two-wire context. -/
def eltAddOp (t : TyT) : TOp [t, t] :=
  TOp.bin Bin2.add t Var.here (Var.there Var.here)

/-- ...and the one-op trace built from it. -/
def eltAddTrace (t : TyT) : Trace t [t, t] :=
  Trace.op (eltAddOp t) (Trace.ret Var.here)

/-- The operand environment read out of an assignment through the layout. -/
def eltEnv {F : Type} {W : Type} (t : TyT) (L : EltLayout t W) (asg : W → F) :
    Env F [t, t] :=
  Env.cons (fun i => asg (L.aw i)) (Env.cons (fun i => asg (L.bw i)) Env.nil)

/-- The claimed output read out of an assignment through the layout. -/
def eltOut {F : Type} {W : Type} (t : TyT) (L : EltLayout t W) (asg : W → F) :
    TVal F t := fun i => asg (L.ow i)

/-- **`eltAddSystem_denotes` — the constraint relation means the denotation.** For
every assignment, the emitted system accepts exactly when the vocabulary's reading
of the one-op trace equals the claimed output.

The scalar reading is *arbitrary* subject to `IsRingReading`: this theorem does not
depend on what the field reading chose for `div`, `pow`, `cmp`, the map tables or
`toIdx`, which is the correct scope for an `add`. -/
theorem eltAddSystem_denotes {F : Type} [Field F] {W : Type} (t : TyT)
    (L : EltLayout t W) (S : ScalarOps F) (hS : IsRingReading S) (asg : W → F) :
    systemAccepts asg (eltAddSystem t L) ↔
      run S (eltAddTrace t) (eltEnv t L asg) = eltOut t L asg := by
  rw [eltAddSystem_accepts_iff]
  constructor
  · intro h
    funext i
    show S.bin Bin2.add (asg (L.aw i)) (asg (L.bw i)) = asg (L.ow i)
    rw [hS.add]
    exact (h i).symm
  · intro h i
    have hi := congrFun h i
    show asg (L.ow i) = asg (L.aw i) + asg (L.bw i)
    rw [← hS.add]
    exact hi.symm

/-- The same statement against the EXECUTOR reading of the DSL (`systemSemHolds`),
by `systemAccepts_iff_systemSemHolds` — rung 1's initiality transfer, consumed
rather than re-proved. -/
theorem eltAddSystem_semHolds_denotes {F : Type} [Field F] {W : Type} (t : TyT)
    (L : EltLayout t W) (S : ScalarOps F) (hS : IsRingReading S) (asg : W → F) :
    systemSemHolds asg (eltAddSystem t L) ↔
      run S (eltAddTrace t) (eltEnv t L asg) = eltOut t L asg := by
  rw [← systemAccepts_iff_systemSemHolds, eltAddSystem_denotes t L S hS]

/-! ## §3. The emitted descriptor, over BabyBear.

Demo shape: a 4-element `f32` vector. Layout over `Fin 12`: the OUTPUT is public at
wires 0–3, operand `a` at 4–7, `b` at 8–11 — the inference-shaped split, where the
claimed answer is what a verifier sees and the operands are committed witness. -/

/-- The BabyBear scalar reading. The four arguments after the two ring-free ones are
placeholders that this path never evaluates — `add` needs only the ring part, which
is exactly what `eltAddSystem_denotes` is stated over. -/
def bbOps : ScalarOps BabyBear :=
  ringOps BabyBear (· / ·) (fun a b => a ^ b.val) (fun _ _ _ => false) (fun _ a => a)
    (fun a => a.val)

theorem bbOps_isRingReading : IsRingReading bbOps :=
  ringOps_isRingReading BabyBear _ _ _ _ _

/-- Demo tensor type: `f32[4]`. -/
def addDemoT : TyT := ⟨Dtype.f32, [4]⟩

/-- The demo wire layout: output public at 0–3, `a` at 4–7, `b` at 8–11. -/
def addDemoLayout : EltLayout addDemoT (Fin 12) where
  ow := fun i => ⟨i.1.val, by omega⟩
  aw := fun i => ⟨4 + i.1.val, by omega⟩
  bw := fun i => ⟨8 + i.1.val, by omega⟩

/-- The demo constraint system — DERIVED by `eltAddSystem`, never a gate list. -/
def addDemoSystem : ConstraintSystem BabyBear (Fin 12) :=
  eltAddSystem addDemoT addDemoLayout

/-- **The emitted descriptor**: `nPublic = 4` (the claimed output), `nVars = 12`. -/
def addDemoDescriptor : ConstraintDescriptor BabyBear :=
  emit Fin.val 4 12 addDemoSystem

/-- *Shape, decided*: four assertions, three gates each (`a+b`, `(−1)·`, `out+`), one
aux wire per gate, four zero-checked roots. The prover sizes its buffers from this
header alone (`emit_wellFormed`, below). -/
theorem addDemoDescriptor_shape :
    addDemoDescriptor.gates.length = 12 ∧ addDemoDescriptor.nWires = 24 ∧
      addDemoDescriptor.zeros.length = 4 := by decide

/-- **`addDemoDescriptor_means_denotation` — the path, closed.** A total wire vector
pinning the variables to `asg` and satisfying the emitted descriptor exists **iff**
`Theory/ZkmlTensorOps`'s denotation of the one-op trace equals the claimed output.

Every step in the chain is a theorem: `emit_accepts_iff_fin` (which rests on
`emit_faithful`, unconditional and both directions) carries the descriptor to the
constraint system, and `eltAddSystem_denotes` carries the constraint system to the
vocabulary's meaning. -/
theorem addDemoDescriptor_means_denotation (asg : Fin 12 → BabyBear) :
    (∃ wv : ℕ → BabyBear, (∀ i : Fin 12, wv i.val = asg i) ∧
        descriptorHolds addDemoDescriptor wv)
      ↔ run bbOps (eltAddTrace addDemoT) (eltEnv addDemoT addDemoLayout asg)
          = eltOut addDemoT addDemoLayout asg :=
  (emit_accepts_iff_fin 12 4 asg addDemoSystem).trans
    (eltAddSystem_denotes addDemoT addDemoLayout bbOps bbOps_isRingReading asg)

/-- The honest assignment: `a = (1,2,3,4)`, `b = (2,3,4,5)`, output `(3,5,7,9)`. -/
def addDemoVals : Fin 12 → BabyBear := ![3, 5, 7, 9, 1, 2, 3, 4, 2, 3, 4, 5]

/-- *Satisfiable, decided*: the honest assignment accepts the derived system. -/
theorem addDemo_accepts : systemAccepts addDemoVals addDemoSystem := by decide

/-- *Satisfiable at the descriptor*: a total wire vector pinning the variables to the
honest assignment satisfies the emitted descriptor — the witness built by
`emit_accepts_iff`, not exhibited by hand. -/
theorem addDemo_descriptor_satisfiable :
    ∃ wv : ℕ → BabyBear, (∀ i : Fin 12, wv i.val = addDemoVals i) ∧
      descriptorHolds addDemoDescriptor wv :=
  (emit_accepts_iff_fin 12 4 addDemoVals addDemoSystem).mpr addDemo_accepts

/-- ...and the honest assignment is one where the DENOTATION holds — the same fact
read through §2, so the satisfying vector above is a vector for a statement about
the vocabulary, not merely about a gate list. -/
theorem addDemo_denotation_holds :
    run bbOps (eltAddTrace addDemoT) (eltEnv addDemoT addDemoLayout addDemoVals)
      = eltOut addDemoT addDemoLayout addDemoVals :=
  (addDemoDescriptor_means_denotation addDemoVals).mp addDemo_descriptor_satisfiable

/-- A forged output: the last element claims `10` where the operands give `9`. -/
def addDemoForged : Fin 12 → BabyBear := ![3, 5, 7, 10, 1, 2, 3, 4, 2, 3, 4, 5]

/-- *Teeth, decided*: **no** total wire vector satisfies the descriptor under the
forged output. A one-element lie in the claimed answer is refused, and by
`addDemoDescriptor_means_denotation` the refusal is a statement about the
vocabulary's denotation — not about a coincidence of gates. -/
theorem addDemo_forged_refused :
    ¬ ∃ wv : ℕ → BabyBear, (∀ i : Fin 12, wv i.val = addDemoForged i) ∧
      descriptorHolds addDemoDescriptor wv := fun h =>
  (by decide : ¬ systemAccepts addDemoForged addDemoSystem)
    ((emit_accepts_iff_fin 12 4 addDemoForged addDemoSystem).mp h)

/-- ...and the forgery fails the DENOTATION too, which is the fact that matters: the
gate system refuses exactly when the tensor semantics refuse. -/
theorem addDemo_forged_denotation_fails :
    ¬ (run bbOps (eltAddTrace addDemoT) (eltEnv addDemoT addDemoLayout addDemoForged)
        = eltOut addDemoT addDemoLayout addDemoForged) := fun h =>
  addDemo_forged_refused ((addDemoDescriptor_means_denotation addDemoForged).mpr h)

/-- *Well-formed*: every emitted wire index is in range and every gate output lands
in the aux region, so a reader can size its buffers from the header. -/
theorem addDemoDescriptor_wellFormed : addDemoDescriptor.WellFormed :=
  emit_wellFormed Fin.val 4 12 (by omega) (fun i => i.isLt) addDemoSystem

/-! ## §4. The conformance artifact.

Written by Lean, read by the unverified prover. The label is the existing one and it
is exact: **vector agreement is the whole claim** — never refinement, never
verification. Rust has no formal semantics, so agreement on emitted vectors is the
entire seam. -/

-- Emit the descriptor as JSON for the Rust side to read. Lean is the only author
-- of this file; the prover only ever reads it.
#eval writeDescriptorJson "prover/testdata/zkml_eltwise_add_descriptor.json"
  addDemoDescriptor

/-! ## §5. Axiom accounting. -/

/-- info: 'Minidregg.Compiler.addDemoDescriptor_means_denotation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms addDemoDescriptor_means_denotation

/-- info: 'Minidregg.Compiler.eltAddSystem_denotes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eltAddSystem_denotes

/-- info: 'Minidregg.Compiler.addDemo_forged_denotation_fails' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms addDemo_forged_denotation_fails

end Minidregg.Compiler
