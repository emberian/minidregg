/-
# Pred.Core — the ONE predicate algebra (ATLAS §7), syntactic AST end-to-end.

This is the foundational policy object of minidregg: a decidable predicate AST over a
name-keyed state/step. It is AST-only by design law — *no opaque functions anywhere in the
policy path*; every policy object is a syntactic tree from day one, so it is serializable,
comparable (`DecidableEq`, kernel-computable), and admits a faithful second reading (circuit,
cost, explainer).

## Why syntactic-only — the N3 trap this file refuses

`Compiler/Signature.lean` proves the converse of N3 (`N3_opaque_payloads_forbid_second_reading`,
faces `OpaqueConflation` / `NoFaithfulSyntacticReading`): a signature whose leaves carry OPAQUE
semantic payloads (`σ → Bool` closures) admits interpretations (`opaqueRun`) with **no faithful
compositional second reading** into any countable/syntactic target — there are `2^ℵ₀` guard
closures and only countably many descriptors, so some pair the executor separates gets one
circuit. Breadstuffs paid for this negatively (`RecStmt.guard : RecordKernelState → Bool` closures
⇒ `compile_not_a_seq_hom`). The law is: guards enter as countable CODES + an eval, never as
function payloads. So **every leaf of `Pred` is first-order data** (slot names, `Int` literals,
finite `Int` sets, a `Vk` identifier). A reviewer may grep this file for `→ Bool` / `→ Prop`
FUNCTION payloads inside the `Pred`/`PredList` inductive: there are NONE. The only arrows are the
`evalWith` oracle argument and the eval functions themselves — never stored in the AST.

## The witnessed escape hatch (four-polarity design)

`witnessed (vk : Vk)` is the third-party-discharged claim leaf — the escape hatch a caveat/intent
polarity needs when a fact is proved OUTSIDE this cell (a credential, a finalized cross-cell read).
It carries an opaque IDENTIFIER (`Vk`, a code/key), NOT a function. The first-party evaluator
`eval` FAILS CLOSED on it (a third-party claim has no first-party discharge). To admit it you must
supply a discharge oracle EXPLICITLY to `evalWith` — the oracle is an argument, never embedded in
the tree, so the AST stays first-order and serializable. (Conceptually the oracle is the trusted,
decidable `Verify` side of `Theory.Knowledge`'s verify/find seam, applied to `vk`.)

## Shape note — why `PredList`, not `List Pred`, inside the node

`all`/`any` are n-ary. To keep evaluation STRUCTURAL (so `decide`/`rfl` reduce in the kernel — no
`native_decide` axiom) and `DecidableEq` DERIVABLE, the recursive children live in a mutually
inductive `PredList` (an inlined `List Pred`), not a nested `List Pred` (whose eval falls to
well-founded recursion, which the kernel will not reduce, and for which `deriving DecidableEq` does
not apply at this Lean pin). `PredList ≃ List Pred` is exhibited (`toList`/`ofList` mutually
inverse), and the user-facing constructors `Pred.all`/`Pred.any` take a genuine `List Pred`, so the
serializable API and the Boolean laws are stated over real lists (`List.all`/`List.any`).

## Faithfulness

The atoms transcribe the SHAPE of breadstuffs' `StateConstraint`/`SimpleConstraint` catalog
(`~/dev/breadstuffs/metatheory/Dregg2/Exec/Program.lean:67+`) — a faithful MINIMAL core:
`fieldEquals` → `eq`, `fieldLe` → `le`, `memberOf` → `memberOf`, `writeOnce` → `writeOnce`,
`monotonic` → `monotone`. Reads are name-keyed and FAIL CLOSED (a missing slot ⇒ the atom is
`false`, except `writeOnce` whose absent-old is the first-write case), mirroring `Value.scalar`.

## Boundary

Core Lean only (Init) — trivially within the Pred boundary {Mathlib, Theory, Pred}.
-/

namespace Minidregg.Pred

/-! ## §1. The state substrate — a name-keyed scalar record, fail-closed reads.

`State` is the concrete record substrate (faithful to breadstuffs' `Value.record`/`Value.scalar`):
a slot is a `String` name, a value is an `Int` scalar, and a read of an absent slot returns `none`
(the fail-closed `Option Int`). `eval` reads OLD and NEW states; the (old, new) pair IS the step. -/

/-- A named slot (a `FieldName` analog). -/
abbrev Slot := String

/-- A state is a name-keyed record of `Int` scalars. Concrete and serializable so the keystone
witnesses are genuine values and `#guard`/`decide` compute on them. -/
structure State where
  /-- The name-keyed scalar cells. -/
  slots : List (Slot × Int)
deriving Repr, DecidableEq

/-- Fail-closed read: the scalar at `k`, or `none` if absent (mirrors `Value.scalar`). -/
def State.get (s : State) (k : Slot) : Option Int :=
  (s.slots.find? (fun p => p.1 == k)).map (·.2)

/-! ## §2. The witnessed leaf's identifier — a code/key, NOT a function.

`Vk` is an opaque IDENTIFIER (a verification-key / claim code). It is the ONLY thing the
`witnessed` leaf carries, which is what keeps the AST first-order: a third-party claim is named
by a code and discharged by an oracle passed to `evalWith`, never by a closure in the tree. -/

/-- An opaque claim/verification-key identifier for a third-party-discharged `witnessed` leaf. -/
structure Vk where
  /-- The identifier code (a content-address / verification-key string). -/
  id : String
deriving Repr, DecidableEq

/-! ## §3. The AST — the ONE predicate algebra.

Decidable atoms over named slots + the Boolean closure (`not`/`all`/`any`) + the `witnessed`
escape hatch. EVERY payload is first-order data — no `→ Bool` / `→ Prop` function anywhere. -/

mutual
/-- **`Pred`** — the ONE predicate algebra, a first-order syntactic AST over an (old, new) step.

Atoms (fail-closed on absent slots): `eq`/`le`/`memberOf`/`monotone` read `new` (`monotone` also
`old`); `writeOnce` reads both. Boolean closure: `not`/`allL`/`anyL` (the latter two over the
inlined `PredList`; use the list-facing smart constructors `Pred.all`/`Pred.any`). Escape hatch:
`witnessed vk`, a third-party claim named by an opaque code, discharged only under an oracle. -/
inductive Pred where
  /-- `new[slot] = value`. -/
  | eq        (slot : Slot) (value : Int)
  /-- `new[slot] ≤ value`. -/
  | le        (slot : Slot) (value : Int)
  /-- `new[slot] ∈ set` (membership in a finite `Int` set). -/
  | memberOf  (slot : Slot) (set : List Int)
  /-- Write-once / register-once: absent-old or `old[slot] = 0` ⇒ any; else `new[slot] = old[slot]`. -/
  | writeOnce (slot : Slot)
  /-- Monotone: `old[slot] ≤ new[slot]` (append-only counter). -/
  | monotone  (slot : Slot)
  /-- **The escape hatch** — a third-party-discharged claim named by the opaque code `vk`.
  First-party `eval` FAILS CLOSED; admission requires an explicit oracle via `evalWith`. -/
  | witnessed (vk : Vk)
  /-- Boolean negation. -/
  | not       (p : Pred)
  /-- Conjunction over the inlined child list (raw constructor; prefer `Pred.all`). -/
  | allL      (ps : PredList)
  /-- Disjunction over the inlined child list (raw constructor; prefer `Pred.any`). -/
  | anyL      (ps : PredList)
/-- An inlined `List Pred` (mutually inductive with `Pred`) — the recursive-child carrier that
keeps evaluation structural and `DecidableEq` derivable. `PredList ≃ List Pred` (see `toList`). -/
inductive PredList where
  /-- Empty. -/
  | nil
  /-- Cons. -/
  | cons (p : Pred) (ps : PredList)
end

deriving instance Repr for Pred, PredList
deriving instance DecidableEq for Pred, PredList

/-- Forget the inlining: `PredList → List Pred`. -/
def PredList.toList : PredList → List Pred
  | .nil       => []
  | .cons p ps => p :: ps.toList

/-- Re-inline: `List Pred → PredList`. -/
def PredList.ofList : List Pred → PredList
  | []      => .nil
  | p :: ps => .cons p (PredList.ofList ps)

/-- A standalone (non-mutual) structural eliminator for `PredList`: the `induction` tactic does
not apply to a mutually-inductive type, so this single-type recursor (recursing on the child list
alone) is provided for proofs/definitions by recursion on a `PredList`. -/
def PredList.rec' {motive : PredList → Sort _} (nil : motive .nil)
    (cons : (p : Pred) → (ps : PredList) → motive ps → motive (.cons p ps)) :
    (ps : PredList) → motive ps
  | .nil       => nil
  | .cons p ps => cons p ps (PredList.rec' nil cons ps)

/-- `toList ∘ ofList = id` — the list view is faithful. -/
@[simp] theorem PredList.toList_ofList (l : List Pred) : (PredList.ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons p ps ih => simp only [PredList.ofList, PredList.toList, ih]

/-- `ofList ∘ toList = id` — the inlining loses nothing (so `PredList ≃ List Pred`). -/
@[simp] theorem PredList.ofList_toList (ps : PredList) : PredList.ofList ps.toList = ps := by
  induction ps using PredList.rec' with
  | nil => rfl
  | cons p rest ih => simp only [PredList.toList, PredList.ofList, ih]

/-- **`Pred.all`** — the list-facing n-ary conjunction (empty ⇒ `true`). The serializable API. -/
def Pred.all (ps : List Pred) : Pred := .allL (PredList.ofList ps)

/-- **`Pred.any`** — the list-facing n-ary disjunction (empty ⇒ `false`). The serializable API. -/
def Pred.any (ps : List Pred) : Pred := .anyL (PredList.ofList ps)

/-! ## §4. The discharge oracle — an ARGUMENT, never a field.

The oracle is how a `witnessed` claim gets discharged. It lives OUTSIDE the AST: it is a parameter
of `evalWith`. This is the whole point of the escape hatch being an identifier rather than a
closure — the tree stays first-order and serializable; only evaluation consults a discharger. -/

/-- A discharge oracle: given a claim code and the (old, new) step, did a third party discharge it?
Passed EXPLICITLY to `evalWith`; NEVER stored in a `Pred`. -/
abbrev Oracle := Vk → State → State → Bool

/-- The fail-closed oracle: no third-party claim is discharged. The first-party `eval` uses it. -/
def failClosed : Oracle := fun _ _ _ => false

/-! ## §5. Evaluation — decidable `Bool`, STRUCTURAL over the AST (so the kernel reduces it).

`evalWith` is the general evaluator (takes an oracle); the mutual `evalWith{All,Any}` recurse
structurally through `PredList`. `eval` is the first-party fragment: `evalWith failClosed`. -/

mutual
  /-- The general evaluator: a decidable `Bool` reading of the AST against an (old, new) step,
  with `witnessed` discharged by the supplied oracle `O`. Every atom fails closed on absent slots. -/
  def evalWith (O : Oracle) (p : Pred) (old new : State) : Bool :=
    match p with
    | .eq s v        => decide (new.get s = some v)
    | .le s v        => match new.get s with
                        | some x => decide (x ≤ v)
                        | none   => false
    | .memberOf s xs => match new.get s with
                        | some x => xs.contains x
                        | none   => false
    | .writeOnce s   => match old.get s with
                        | none   => true
                        | some o => o == 0 || decide (new.get s = some o)
    | .monotone s    => match old.get s, new.get s with
                        | some o, some n => decide (o ≤ n)
                        | _,      _      => false
    | .witnessed vk  => O vk old new
    | .not q         => !(evalWith O q old new)
    | .allL ps       => evalWithAll O ps old new
    | .anyL ps       => evalWithAny O ps old new
  /-- Conjunction fold over `PredList` (empty ⇒ `true`). -/
  def evalWithAll (O : Oracle) (ps : PredList) (old new : State) : Bool :=
    match ps with
    | .nil        => true
    | .cons q rest => evalWith O q old new && evalWithAll O rest old new
  /-- Disjunction fold over `PredList` (empty ⇒ `false`). -/
  def evalWithAny (O : Oracle) (ps : PredList) (old new : State) : Bool :=
    match ps with
    | .nil        => false
    | .cons q rest => evalWith O q old new || evalWithAny O rest old new
end

/-- **`eval`** — the first-party fragment: `witnessed` fails closed (no oracle). -/
def eval (p : Pred) (old new : State) : Bool :=
  evalWith failClosed p old new

/-! ## §6. The Boolean structure — `not`/`all`/`any` denote `!`/`List.all`/`List.any`. -/

/-- The conjunction fold over `ofList l` IS `List.all` of the evaluated children. -/
theorem evalWithAll_ofList (O : Oracle) (l : List Pred) (old new : State) :
    evalWithAll O (PredList.ofList l) old new = l.all (fun q => evalWith O q old new) := by
  induction l with
  | nil => rfl
  | cons q rest ih => simp only [PredList.ofList, evalWithAll, List.all_cons, ih]

/-- The disjunction fold over `ofList l` IS `List.any` of the evaluated children. -/
theorem evalWithAny_ofList (O : Oracle) (l : List Pred) (old new : State) :
    evalWithAny O (PredList.ofList l) old new = l.any (fun q => evalWith O q old new) := by
  induction l with
  | nil => rfl
  | cons q rest ih => simp only [PredList.ofList, evalWithAny, List.any_cons, ih]

/-- `evalWith (not p) = !evalWith p`. -/
@[simp] theorem evalWith_not (O : Oracle) (p : Pred) (old new : State) :
    evalWith O (.not p) old new = !(evalWith O p old new) := by
  simp only [evalWith]

/-- **`evalWith (Pred.all ps) = List.all`** of the evaluated children. -/
@[simp] theorem evalWith_all (O : Oracle) (ps : List Pred) (old new : State) :
    evalWith O (Pred.all ps) old new = ps.all (fun q => evalWith O q old new) := by
  simp only [Pred.all, evalWith, evalWithAll_ofList]

/-- **`evalWith (Pred.any ps) = List.any`** of the evaluated children. -/
@[simp] theorem evalWith_any (O : Oracle) (ps : List Pred) (old new : State) :
    evalWith O (Pred.any ps) old new = ps.any (fun q => evalWith O q old new) := by
  simp only [Pred.any, evalWith, evalWithAny_ofList]

/-- **`eval (not p) = !eval p`** — the first-party Boolean law. -/
theorem eval_not (p : Pred) (old new : State) :
    eval (.not p) old new = !(eval p old new) :=
  evalWith_not failClosed p old new

/-- **`eval (Pred.all ps) = List.all`** — the first-party Boolean law. -/
theorem eval_all (ps : List Pred) (old new : State) :
    eval (Pred.all ps) old new = ps.all (fun q => eval q old new) :=
  evalWith_all failClosed ps old new

/-- **`eval (Pred.any ps) = List.any`** — the first-party Boolean law. -/
theorem eval_any (ps : List Pred) (old new : State) :
    eval (Pred.any ps) old new = ps.any (fun q => eval q old new) :=
  evalWith_any failClosed ps old new

/-! ## §7. The KEYSTONE — non-vacuity + teeth (ATLAS design-law 2).

A keystone that cannot exhibit both poles does not compile. We do NOT assert non-vacuity; we
BUILD the witnesses (the 2026-08-07 audit-discipline lesson): a concrete satisfying step, a
concrete state pair where a specific atom fires TRUE, and a hostile pair where the SAME atom fires
FALSE — so the atoms genuinely decide (they are neither vacuously true nor constant), each
discharged by `decide` so the decidability is a KERNEL computation, not a claim. -/

/-- A pre-state: `x = 3`, `y = 10`. -/
def sX3 : State := ⟨[("x", 3), ("y", 10)]⟩

/-- A post-state: `x = 5`, `y = 10` (x grew). -/
def sX5 : State := ⟨[("x", 5), ("y", 10)]⟩

/-- A compound policy exercising every closure and four atoms:
`y` pinned to 10, `x ≤ 5`, `x ∈ {3,5,7}`, and `x` monotone across the step. -/
def demoPred : Pred :=
  Pred.all [.eq "y" 10, .le "x" 5, .memberOf "x" [3, 5, 7], .monotone "x"]

/-- **Satisfiable** (non-vacuity): the algebra ACCEPTS a concrete step (`sX3 → sX5`). Built,
not asserted — `decide` runs the evaluator to `true`. -/
theorem demo_satisfiable : eval demoPred sX3 sX5 = true := by decide

/-- **Hostile pole**: on the SWAPPED (hostile) step `sX5 → sX3`, `x` decreases, so `monotone`
fails and the whole conjunction REJECTS — the same policy discriminates. -/
theorem demo_rejects_hostile : eval demoPred sX5 sX3 = false := by decide

/-- **Tooth — fires TRUE**: `monotone "x"` on `sX3 → sX5` (3 ≤ 5). -/
theorem monotone_tooth_fires : eval (.monotone "x") sX3 sX5 = true := by decide

/-- **Tooth — refuses on the hostile pair**: the SAME atom `monotone "x"` on the swapped step
`sX5 → sX3` (5 ≤ 3 is false). One atom, both poles: genuine decision, not a vacuous constant. -/
theorem monotone_tooth_refuses : eval (.monotone "x") sX5 sX3 = false := by decide

/-- **Witnessed escape-hatch tooth — first party fails closed**: with no oracle, a third-party
claim is refused. -/
theorem witnessed_firstparty_refuses : eval (.witnessed ⟨"vk-1"⟩) sX3 sX5 = false := by decide

/-- **Witnessed escape-hatch tooth — a granting oracle discharges it**: the SAME AST leaf admits
under a discharging oracle supplied to `evalWith`. The oracle toggles the outcome and is never in
the tree — exactly the escape hatch's design. -/
theorem witnessed_discharged_fires :
    evalWith (fun _ _ _ => true) (.witnessed ⟨"vk-1"⟩) sX3 sX5 = true := by decide

/-- **The keystone** (ATLAS design-law 2): the algebra is non-vacuous (a concrete step is
accepted) AND a single atom exhibits BOTH poles (fires on one step, refuses on the hostile one)
AND the witnessed escape hatch genuinely toggles (fail-closed vs. discharged). All fields are
BUILT witnesses, discharged by `decide`. -/
def keystone : Prop :=
  (∃ old new, eval demoPred old new = true) ∧          -- satisfiable (non-vacuous)
  (eval (.monotone "x") sX3 sX5 = true) ∧              -- tooth fires
  (eval (.monotone "x") sX5 sX3 = false) ∧             -- SAME atom, hostile pair refuses
  (eval (.witnessed ⟨"vk-1"⟩) sX3 sX5 = false) ∧       -- escape hatch: first-party fail-closed
  (evalWith (fun _ _ _ => true) (.witnessed ⟨"vk-1"⟩) sX3 sX5 = true)  -- discharged by oracle

/-- The keystone holds — witnesses supplied, not asserted. -/
theorem keystone_holds : keystone := by
  refine ⟨⟨sX3, sX5, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §8. Genuine decidability — exercised by `#guard` (silent `native_decide`, confessed).

Per ATLAS design-law 9, `#guard` is a compiled non-vacuity WITNESS, not a theorem — the theorems
above (`by decide`, kernel-checked) carry the content; these guards confess that the evaluator and
the derived `DecidableEq` actually COMPUTE on concrete instances. -/

-- The evaluator computes:
#guard eval demoPred sX3 sX5 = true
#guard eval demoPred sX5 sX3 = false
#guard eval (.monotone "x") sX3 sX5 = true
#guard eval (.monotone "x") sX5 sX3 = false
#guard eval (.witnessed ⟨"vk-1"⟩) sX3 sX5 = false
#guard evalWith (fun _ _ _ => true) (.witnessed ⟨"vk-1"⟩) sX3 sX5 = true
-- fail-closed reads: absent slot ⇒ atom false
#guard eval (.eq "absent" 0) sX3 sX5 = false
#guard eval (.le "absent" 99) sX3 sX5 = false
-- write-once: absent old ⇒ first write admitted; changing a set nonzero value ⇒ refused
#guard eval (.writeOnce "x") ⟨[]⟩ sX5 = true
#guard eval (.writeOnce "x") sX3 sX5 = false
-- membership atom, both poles
#guard eval (.memberOf "x" [3, 5, 7]) sX3 sX5 = true
#guard eval (.memberOf "x" [1, 2]) sX3 sX5 = false
-- the derived DecidableEq on the AST computes (syntactic equality is decidable):
#guard decide (demoPred = demoPred) = true
#guard decide (Pred.eq "x" 5 = Pred.eq "x" 6) = false
#guard decide (Pred.witnessed ⟨"a"⟩ = Pred.witnessed ⟨"b"⟩) = false

/-- The derived `DecidableEq Pred` is exercised by the kernel too. -/
example : (demoPred = demoPred) := by decide

/-- Distinct atoms are decidably distinct. -/
example : (Pred.eq "x" 5 ≠ Pred.eq "x" 6) := by decide

end Minidregg.Pred
