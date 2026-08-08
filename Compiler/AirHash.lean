/-
# `Compiler/AirHash.lean` — [AIR-poseidon]: the hash-permutation gadget, DERIVED through the DSL

A note-spend needs `nullifier = hash(note)` as a CONSTRAINT. The hash is a Poseidon2-style
round permutation: each round adds round constants, applies the S-box `x ^ α` (all wires in a
full round, wire 0 only in a partial round), then a linear layer (matrix-vector product); the
permutation is the composition of the round schedule. This file grows that gadget on the
`Compiler/Air` rung, PARAMETERIZED over `(w, α, round constants, matrices, full/partial
schedule)` — the STRUCTURE is the theorem; a concrete parameter set is one instantiation.

**Substrate, said out loud: this is Lean-authored arithmetization.** Every wire of the
permutation is a `Term (AirSig F Idx)` built from the DSL surface (`vr`/`cst`/`add'`/`mul'`)
and read through the one fold (`eval = fold evalAlg`); the constraint is a
`ConstraintSystem`; its meaning comes from rung 1's initiality keystone
(`accepts_iff_semHolds` / `eval_agrees_exec`) — reused, never re-derived. NO constraint is
hand-authored outside the DSL: no Rust (`cert_f_air` and its siblings are the debt this
replaces), no bespoke `air_accepts`, no parallel executor smuggled in as truth.

## The construction

* `sbox α e` — `e ^ α` by repeated `mul'` (`x·x·…·x`, `α − 1` gates);
* `addConst c e` — `e + c`;
* `linearLayer M state` — each new wire `i` is `Σⱼ Mᵢⱼ·(state j)`, the weighted sum folded
  from DSL constructors over `List.finRange w` (the `AirRange.weightedSum` pattern);
* `roundFn α r state` — one round: add `r.rc`, S-box (`r.full` selects all wires vs wire 0),
  then `r.M` — per-round matrices subsume Poseidon2's external/internal matrix split;
* `permGadget spec state` — the round schedule composed by `List.foldl`.

The EXECUTOR (`permExec`, via `roundExec`/`sboxLayerExec`) is an independent reference
permutation on `Fin w → F` — pure field arithmetic (`^`, `∑`, `+`), no terms, no `eval`.

## Statement-first (the ATLAS fields)

* `permGadget_eval` — the keystone: the CIRCUIT evaluation of the gadget equals the EXECUTOR
  permutation of the evaluated inputs, for EVERY spec, EVERY state, EVERY assignment — all
  `R` rounds, by one list induction over the schedule with each round's agreement falling out
  of the definitional computation rules of the fold (`eval_add'`/`eval_mul'` are `rfl` by
  `fold_mk`). `permGadget_evalExec` restates it against `evalExec`, the genuinely independent
  term-executor, via `eval_agrees_exec` — circuit ⟺ executor, no drift possible.
* `hashConstraint_correct` — the note connection: the system accepts `asg` IFF
  `asg nullifier = hashExec spec (asg ∘ note)` (first output wire, sponge-style). Teeth
  (`hashConstraint_teeth`): any assignment whose nullifier wire differs from the hash is
  REJECTED — the constraint binds the preimage. Premise-inhabitation
  (`hashConstraint_complete`): every note has its accepting assignment.
* Keystone witnesses, BUILT over `ZMod 13` (`w = 2`, `α = 5` — `gcd(5, 12) = 1`, so the
  S-box is a genuine permutation of the field; 3 rounds: full, partial, full): the executor
  computes (`permExec = ![4, 3]` on note `(4, 9)`); circuit ⟺ executor computed against the
  REAL fold; the true nullifier accepts; a wrong nullifier is rejected; a wrong NOTE under
  the true nullifier is rejected; EVERY accepted nullifier equals the hash (derived from the
  iff, not enumerated).

## Honest scope — what this file does NOT claim

* `[AIR-poseidon-params]` RESIDUAL: the deployed Poseidon2 parameter set (width, the real
  round constants and MDS/internal matrices, the round counts from the security analysis,
  the initial external-matrix multiplication — expressible as `linearLayer M input` before
  `permGadget`) and the sponge mode (rate/capacity split, padding, multi-block absorption).
  The demo instance here exercises the structure; it is NOT a deployed parameter set.
* `[COMMIT-CR]` FLOOR: this gadget COMPUTES the permutation; that the resulting hash is
  collision-resistant / hiding is a cryptographic ASSUMPTION about the instantiated
  parameters, outside every theorem below — named, not smuggled.
* Degree: the S-box emits degree-`α` terms; bounded-degree gate form is `[AIR-flatten]`'s
  closed rung (`Compiler/AirFlatten`), applied downstream, not re-proved here.
-/
import Compiler.AirRange

namespace Minidregg.Compiler

universe u

variable {F : Type u} [Field F] {Idx : Type u} {w : ℕ}

/-! ## §1. The parameter space — a round, a schedule. -/

/-- One round's parameters: its round constants, whether it is a FULL round (S-box every
wire) or a PARTIAL round (S-box wire 0 only), and its linear layer. Per-round matrices
subsume Poseidon2's external/internal matrix distinction. -/
structure Round (F : Type u) (w : ℕ) where
  /-- The round constants, one per wire. -/
  rc : Fin w → F
  /-- `true`: full round (S-box all wires); `false`: partial round (S-box wire 0 only). -/
  full : Bool
  /-- The linear layer applied after the S-box. -/
  M : Fin w → Fin w → F

/-- A permutation spec: the S-box exponent and the round schedule. Poseidon2 is one
instantiation of this space (`[AIR-poseidon-params]` carries its deployed values). -/
structure PermSpec (F : Type u) (w : ℕ) where
  /-- The S-box exponent (`α = 5` typical). -/
  α : ℕ
  /-- The round schedule, in application order. -/
  rounds : List (Round F w)

/-! ## §2. The GADGET — every wire a DSL term, built from `vr`/`cst`/`add'`/`mul'`. -/

/-- The S-box `e ^ a`, as repeated `mul'` (`x·x·…·x` — `a − 1` multiplication gates;
`a = 0` degenerates to the constant `1`). -/
def sbox (a : ℕ) (e : Term (AirSig F Idx)) : Term (AirSig F Idx) :=
  match a with
  | 0 => cst 1
  | 1 => e
  | n + 2 => mul' e (sbox (n + 1) e)

/-- Add a round constant: `e + c`. -/
def addConst (c : F) (e : Term (AirSig F Idx)) : Term (AirSig F Idx) :=
  add' e (cst c)

/-- The linear layer: new wire `i` is `Σⱼ Mᵢⱼ·(state j)`, the weighted sum folded from DSL
constructors over `List.finRange w` (the `weightedSum` pattern of `AirRange`). -/
def linearLayer (M : Fin w → Fin w → F) (state : Fin w → Term (AirSig F Idx)) :
    Fin w → Term (AirSig F Idx) :=
  fun i => (List.finRange w).foldr
    (fun j acc => add' (mul' (cst (M i j)) (state j)) acc) (cst 0)

/-- The S-box layer: full rounds S-box every wire, partial rounds wire 0 only. -/
def sboxLayer (a : ℕ) (full : Bool) (state : Fin w → Term (AirSig F Idx)) :
    Fin w → Term (AirSig F Idx) :=
  fun i => if full = true ∨ (i : ℕ) = 0 then sbox a (state i) else state i

/-- **One round of the permutation**: add round constants, S-box, linear layer. -/
def roundFn (a : ℕ) (r : Round F w) (state : Fin w → Term (AirSig F Idx)) :
    Fin w → Term (AirSig F Idx) :=
  linearLayer r.M (sboxLayer a r.full fun i => addConst (r.rc i) (state i))

/-- **The permutation gadget**: the round schedule composed by `foldl` — a genuine derived
object, every output wire a term of the DSL. -/
def permGadget (spec : PermSpec F w) (state : Fin w → Term (AirSig F Idx)) :
    Fin w → Term (AirSig F Idx) :=
  spec.rounds.foldl (fun st r => roundFn spec.α r st) state

/-! ## §3. The EXECUTOR — the independent reference permutation on `Fin w → F`.

Pure field arithmetic: `^` for the S-box, `∑` for the linear layer, `foldl` over the same
schedule. No terms, no `eval` — the semantics the circuit must match. -/

/-- Executor S-box layer: `x ^ a` on the S-boxed wires. -/
def sboxLayerExec (a : ℕ) (full : Bool) (st : Fin w → F) : Fin w → F :=
  fun i => if full = true ∨ (i : ℕ) = 0 then st i ^ a else st i

/-- Executor round: constants, S-box, matrix — as field arithmetic. -/
def roundExec (a : ℕ) (r : Round F w) (st : Fin w → F) : Fin w → F :=
  fun i => ∑ j : Fin w, r.M i j * sboxLayerExec a r.full (fun j' => st j' + r.rc j') j

/-- **The executor permutation** — the reference the gadget is proved against. -/
def permExec (spec : PermSpec F w) (st : Fin w → F) : Fin w → F :=
  spec.rounds.foldl (fun st r => roundExec spec.α r st) st

/-- The hash of a `w`-wire note: the FIRST output wire of the permutation (sponge-style
squeeze of one element; rate/capacity discipline is `[AIR-poseidon-params]`). -/
def hashExec [NeZero w] (spec : PermSpec F w) (note : Fin w → F) : F :=
  permExec spec note 0

/-! ## §4. CIRCUIT ⟺ EXECUTOR — the keystone, all `R` rounds.

Each computation rule of the fold is `rfl` (`fold_mk`), so a round's agreement is
definitional unfolding plus `eval_sbox`/`eval_linearLayer`; the schedule composes by one
list induction. `permGadget_evalExec` then transfers the whole statement to `evalExec` —
the independent term-executor — by `eval_agrees_exec`, rung 1's initiality. -/

/-- The circuit reads the S-box as `^`. -/
@[simp] theorem eval_sbox (asg : Idx → F) :
    ∀ (a : ℕ) (e : Term (AirSig F Idx)), eval asg (sbox a e) = eval asg e ^ a
  | 0, e => by simp [sbox]
  | 1, e => by simp [sbox]
  | n + 2, e => by
    simp [sbox, eval_sbox asg (n + 1) e, pow_succ']

/-- The circuit reads `addConst` as `+`. -/
@[simp] theorem eval_addConst (asg : Idx → F) (c : F) (e : Term (AirSig F Idx)) :
    eval asg (addConst c e) = eval asg e + c := rfl

private theorem eval_linFold (asg : Idx → F) (row : Fin w → F)
    (state : Fin w → Term (AirSig F Idx)) :
    ∀ l : List (Fin w),
      eval asg (l.foldr (fun j acc => add' (mul' (cst (row j)) (state j)) acc) (cst 0))
        = (l.map fun j => row j * eval asg (state j)).sum
  | [] => by simp
  | j :: l => by simp [eval_linFold asg row state l]

/-- The circuit reads the linear layer as the matrix-vector product. -/
theorem eval_linearLayer (asg : Idx → F) (M : Fin w → Fin w → F)
    (state : Fin w → Term (AirSig F Idx)) (i : Fin w) :
    eval asg (linearLayer M state i) = ∑ j : Fin w, M i j * eval asg (state j) := by
  unfold linearLayer
  rw [eval_linFold, Fin.sum_univ_def]

/-- The circuit reads the S-box layer as the executor's. -/
theorem eval_sboxLayer (asg : Idx → F) (a : ℕ) (full : Bool)
    (state : Fin w → Term (AirSig F Idx)) (i : Fin w) :
    eval asg (sboxLayer a full state i)
      = sboxLayerExec a full (fun j => eval asg (state j)) i := by
  unfold sboxLayer sboxLayerExec
  by_cases h : full = true ∨ (i : ℕ) = 0 <;> simp [h]

/-- **One round, circuit ⟺ executor**: evaluating the round gadget is the executor round on
the evaluated state. -/
theorem eval_roundFn (asg : Idx → F) (a : ℕ) (r : Round F w)
    (state : Fin w → Term (AirSig F Idx)) :
    (fun i => eval asg (roundFn a r state i)) = roundExec a r fun i => eval asg (state i) := by
  funext i
  unfold roundFn roundExec
  rw [eval_linearLayer]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_sboxLayer]
  rfl

private theorem eval_permFold (asg : Idx → F) (a : ℕ) :
    ∀ (l : List (Round F w)) (state : Fin w → Term (AirSig F Idx)),
      (fun i => eval asg (l.foldl (fun st r => roundFn a r st) state i))
        = l.foldl (fun st r => roundExec a r st) fun i => eval asg (state i)
  | [], _ => rfl
  | r :: l, state => by
    rw [List.foldl_cons, List.foldl_cons, eval_permFold asg a l (roundFn a r state),
      eval_roundFn]

/-- **`permGadget_eval` — CIRCUIT ⟺ EXECUTOR for the whole permutation.** For every spec,
state, and assignment: evaluating the gadget's output wires IS the executor permutation of
the evaluated input wires — all `R` rounds, every full/partial schedule, every matrix. -/
theorem permGadget_eval (asg : Idx → F) (spec : PermSpec F w)
    (state : Fin w → Term (AirSig F Idx)) :
    (fun i => eval asg (permGadget spec state i))
      = permExec spec fun i => eval asg (state i) :=
  eval_permFold asg spec.α spec.rounds state

/-- Pointwise form (the shape `rw` consumes). -/
theorem permGadget_eval_apply (asg : Idx → F) (spec : PermSpec F w)
    (state : Fin w → Term (AirSig F Idx)) (i : Fin w) :
    eval asg (permGadget spec state i) = permExec spec (fun j => eval asg (state j)) i :=
  congrFun (permGadget_eval asg spec state) i

/-- **The same agreement against `evalExec`** — the INDEPENDENT term-executor of rung 1 —
via `eval_agrees_exec` (initiality): the hand-recursed reading of the gadget also computes
the reference permutation. Circuit, term-executor, and reference permutation all coincide. -/
theorem permGadget_evalExec (asg : Idx → F) (spec : PermSpec F w)
    (state : Fin w → Term (AirSig F Idx)) :
    (fun i => evalExec asg (permGadget spec state i))
      = permExec spec fun i => evalExec asg (state i) := by
  rw [eval_agrees_exec]
  exact permGadget_eval asg spec state

/-! ## §5. The HASH CONSTRAINT — `nullifier ≐ hash(note)`, and what it binds. -/

/-- The hash assertion: `permGadget(note wires)₀ − nullifier ≐ 0`. -/
def hashTerm [NeZero w] (spec : PermSpec F w) (nullifier : Idx) (note : Fin w → Idx) :
    Term (AirSig F Idx) :=
  add' (permGadget spec (fun i => vr (note i)) 0) (mul' (cst (-1)) (vr nullifier))

/-- **The hash constraint** `[AIR-poseidon]`: the system asserting
`nullifier = hash(note)`. One assertion; composes with `rangeGadget` (amounts) and the
`[AIR-membership]` circuit by list append. -/
def hashConstraint [NeZero w] (spec : PermSpec F w) (nullifier : Idx) (note : Fin w → Idx) :
    ConstraintSystem F Idx :=
  [hashTerm spec nullifier note]

/-- The assertion means the equation: it accepts iff the nullifier wire carries EXACTLY the
executor hash of the note wires. -/
theorem hashTerm_correct [NeZero w] (asg : Idx → F) (spec : PermSpec F w)
    (nullifier : Idx) (note : Fin w → Idx) :
    accepts asg (hashTerm spec nullifier note) ↔
      asg nullifier = hashExec spec fun i => asg (note i) := by
  unfold accepts hashTerm hashExec
  rw [eval_add', eval_mul', eval_cst, eval_vr, permGadget_eval_apply, neg_one_mul,
    add_neg_eq_zero]
  exact eq_comm

/-- **`hashConstraint_correct` — the keystone iff.** The constraint system accepts `asg`
IFF `asg nullifier = hashExec spec (asg ∘ note)`. Sound AND complete: nothing but the hash
equation is imposed, and the hash equation is fully imposed. (That the hash is hard to
invert or collide is `[COMMIT-CR]`, a cryptographic floor about the PARAMETERS — no theorem
here claims it.) -/
theorem hashConstraint_correct [NeZero w] (asg : Idx → F) (spec : PermSpec F w)
    (nullifier : Idx) (note : Fin w → Idx) :
    systemAccepts asg (hashConstraint spec nullifier note) ↔
      asg nullifier = hashExec spec fun i => asg (note i) := by
  unfold systemAccepts hashConstraint
  rw [List.forall_mem_singleton]
  exact hashTerm_correct asg spec nullifier note

/-- The EXECUTOR reading of the keystone, by rung 1's initiality transfer — the semantic
relation of the hash system is the same equation. -/
theorem hashConstraint_semHolds_correct [NeZero w] (asg : Idx → F) (spec : PermSpec F w)
    (nullifier : Idx) (note : Fin w → Idx) :
    systemSemHolds asg (hashConstraint spec nullifier note) ↔
      asg nullifier = hashExec spec fun i => asg (note i) := by
  rw [← systemAccepts_iff_systemSemHolds, hashConstraint_correct]

/-- **Teeth, general form**: an assignment whose nullifier wire is NOT the hash of its note
wires is REJECTED — the constraint binds the preimage, for every spec and assignment. -/
theorem hashConstraint_teeth [NeZero w] (asg : Idx → F) (spec : PermSpec F w)
    (nullifier : Idx) (note : Fin w → Idx)
    (h : asg nullifier ≠ hashExec spec fun i => asg (note i)) :
    ¬ systemAccepts asg (hashConstraint spec nullifier note) :=
  fun hacc => h ((hashConstraint_correct asg spec nullifier note).mp hacc)

/-- **Premise-inhabitation / completeness**: EVERY note has its accepting assignment — the
note values on the note wires, the computed hash on the nullifier wire. The iff of
`hashConstraint_correct` has teeth in both directions. -/
theorem hashConstraint_complete [NeZero w] (spec : PermSpec F w) (noteVals : Fin w → F) :
    ∃ asg : Option (ULift.{u} (Fin w)) → F,
      (∀ i, asg (some (ULift.up i)) = noteVals i) ∧
        asg none = hashExec spec noteVals ∧
        systemAccepts asg (hashConstraint spec none fun i => some (ULift.up i)) := by
  refine ⟨fun o => match o with
    | none => hashExec spec noteVals
    | some i => noteVals i.down, fun _ => rfl, rfl, ?_⟩
  rw [hashConstraint_correct]

/-! ## §6. Keystone witnesses — BUILT over `ZMod 13`, `w = 2`, `α = 5`, 3 rounds
(full · partial · full), all computing against the REAL fold via §1 of `AirRange`'s
`Decidable` instances.

`α = 5` over `ZMod 13` is a genuine S-box (`gcd(5, 12) = 1`, so `x ^ 5` permutes the
field — over `ZMod 11` it would collapse to `{0, ±1}`). The constants/matrix here are a
DEMO instantiation exercising both round kinds; the deployed set is
`[AIR-poseidon-params]`. -/

instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- Demo linear layer (invertible over `ZMod 13`: det `= 5 ≠ 0`). -/
def demoM : Fin 2 → Fin 2 → ZMod 13 := ![![2, 1], ![1, 3]]

/-- The demo spec: `α = 5`; rounds full (rc `(3,5)`), partial (rc `(1,7)`), full
(rc `(2,4)`). -/
def demoSpec : PermSpec (ZMod 13) 2 where
  α := 5
  rounds :=
    [ ⟨![3, 5], true,  demoM⟩,
      ⟨![1, 7], false, demoM⟩,
      ⟨![2, 4], true,  demoM⟩ ]

/-- Demo wire index: `none` the nullifier wire, `some i` the note wires. -/
def hashAsg (nullifier : ZMod 13) (note : Fin 2 → ZMod 13) : Option (Fin 2) → ZMod 13 :=
  fun o => match o with
  | none => nullifier
  | some i => note i

/-- *The executor computes*: the reference permutation of note `(4, 9)` is `(4, 3)`. -/
example : permExec demoSpec ![4, 9] = ![4, 3] := by decide

/-- *Circuit ⟺ executor, COMPUTED*: the gadget's wires evaluate to the reference
permutation on a concrete input — the agreement theorem exercised end-to-end against the
real fold, not a hand mirror. -/
example : (fun i => eval (![4, 9] : Fin 2 → ZMod 13) (permGadget demoSpec vr i))
    = permExec demoSpec ![4, 9] := by decide

/-- *The hash computes*: `hash(4, 9) = 4`. -/
example : hashExec demoSpec ![4, 9] = 4 := by decide

/-- *Satisfiable, computed*: note `(4, 9)` with its TRUE nullifier `4` accepts. -/
example : systemAccepts (hashAsg 4 ![4, 9]) (hashConstraint demoSpec none some) := by
  decide

/-- *Teeth (wrong nullifier), computed*: nullifier `5 ≠ hash(4, 9)` is REJECTED. -/
example : ¬ systemAccepts (hashAsg 5 ![4, 9]) (hashConstraint demoSpec none some) := by
  decide

/-- *Teeth (wrong note), computed*: the SAME nullifier `4` with a different note `(5, 9)`
(whose hash is `1`) is REJECTED — the constraint binds the preimage side too. -/
example : ¬ systemAccepts (hashAsg 4 ![5, 9]) (hashConstraint demoSpec none some) := by
  decide

/-- *The teeth are the iff's, not an enumeration*: EVERY accepted nullifier for note
`(4, 9)` equals the hash — derived from `hashConstraint_correct`, closed over all 13 field
values at once. -/
example (nf : ZMod 13)
    (h : systemAccepts (hashAsg nf ![4, 9]) (hashConstraint demoSpec none some)) :
    nf = 4 := by
  have hb := (hashConstraint_correct (hashAsg nf ![4, 9]) demoSpec none some).mp h
  have hv : hashExec demoSpec ![4, 9] = 4 := by decide
  exact hb.trans hv

/-- *Completeness, instantiated*: the generic witness builder lands on the demo spec. -/
example : ∃ asg : Option (ULift (Fin 2)) → ZMod 13,
    (∀ i, asg (some (ULift.up i)) = (![4, 9] : Fin 2 → ZMod 13) i) ∧
      asg none = hashExec demoSpec ![4, 9] ∧
      systemAccepts asg (hashConstraint demoSpec none fun i => some (ULift.up i)) :=
  hashConstraint_complete demoSpec ![4, 9]

/-! ### Honest residuals — the rungs above this one (named, none stubbed)

`[AIR-poseidon-params]` — the deployed parameter set: real Poseidon2 width/constants/
matrices/round counts (from the published security analysis), the initial external-matrix
multiplication (`permGadget spec (linearLayer M_E input)` — expressible today, the VALUES
are the residual), and the sponge mode (rate/capacity, padding, multi-block absorption for
notes wider than the rate). Structure is closed here; values are instantiation.

`[COMMIT-CR]` — collision resistance / preimage security of the instantiated hash is a
cryptographic ASSUMPTION (a floor, like FRI's), never a theorem of this file: the gadget
COMPUTES the permutation, `hashConstraint_correct` says the constraint imposes exactly the
hash equation, and nothing here claims the equation is hard to satisfy dishonestly.

`[AIR-membership]` — the Merkle-path gadget (this file's `hashConstraint` composed along a
path), the remaining note-spend constraint. `[AIR-sumcheck]` unchanged upstream. -/

end Minidregg.Compiler
