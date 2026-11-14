/-
# Assurance.CitedLand — a verdict cell, and a land that cites it

The first consumer of cited reads (`citedRead`, `Payload.fieldRead` in `Kernel/ResourceTransaction.lean`) and of a
joint participant's identity (`DeclaredResourceController.identitySlots`). Two law templates under
`native/resource-client/templates/fleet`, embedded here as `Pred` terms by `scripts/gen-sheetlaw.py`
(§2 is generated; `--check` compares it with the JSON):

* `verdict/law.verdict`: a verdict is written once, by the producer it names, and a result other
  than unread needs a red control (`verdict_signed_by_producer`, `verdict_written_once`,
  `verdict_result_needs_red_control`).
* `branch/law.branch`: a branch head moves only in a turn that cites, at joint position 1, a
  verdict cell born under the verdict room and committed to the verdict law, passing, for exactly
  the new head, whose recorded read set is the digest of the footprint the turn cites at position
  2 (`land_needs_current_passing_verdict`).

What the law does not check, the kernel does: the footprint at position 2 is compared by value
with the loaded cell, and a land whose cited fields moved is refused naming every moved field.
§4 is that sequence on `citedRead` itself, at concrete stores: admitted; refused naming both moved
fields (and only the one, when one moved); admitted again once the values are back, at a store
that differs elsewhere (`land_footprint_scenario`).

Scope. §3 and §5 are about the two laws as predicates. §4 is about `citedRead`, for any authority
snapshot whose grant names the cited fields (`granted`); no snapshot is constructed here, and no
`PreparedInvocation` is: that the controller hands these laws the slots §5 writes out is
`DeclaredResourceController.joint_identity_exact` and `ResourceTransaction.citedProject`
(`cited_digest_slot`), not a theorem of this file. The digest in §5's states is a stand-in integer;
the laws only compare it for equality.
-/
import Pred.Core
import Kernel.LawView
import Kernel.ResourceTransaction
import Theory.AssertAxioms

namespace Minidregg.Assurance.CitedLand

open Minidregg.Pred (Pred State eval)
open Minidregg.Kernel.LawView
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

/-! ## §1. What a branch law is instantiated at -/

structure Params where
  /-- The cell every verdict is born under. -/
  VERDICTS : Int
  /-- The address of the verdict law (`cell/law` of every verdict cell). -/
  VERDICT_LAW : Int

/-! ## §2. The laws, literally (`fleet/verdict/law.verdict.json`, `fleet/branch/law.branch.json`) -/

section Law
set_option linter.unusedVariables false

/-- clause 0 -/
def verdictClause0 (p : Params) : Pred :=
  Pred.any [
    .eq "request/verb" 1,
    .eq "request/verb" 2]

/-- clause 1 -/
def verdictClause1 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .eqSlots "request/subject" "resource/field/3/after"]

/-- clause 2 -/
def verdictClause2 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    Pred.all [
      .writeOnce "resource/field/0/after",
      .writeOnce "resource/field/1/after",
      .writeOnce "resource/field/2/after",
      .writeOnce "resource/field/3/after",
      .writeOnce "resource/field/4/after"]]

/-- clause 3 -/
def verdictClause3 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    Pred.all [
      .memberOf "resource/field/1/after" [1, 2, 3],
      .memberOf "resource/field/2/after" [1, 2, 3]]]

/-- clause 4 -/
def verdictClause4 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .eq "resource/field/1/after" 1,
    .eq "resource/field/2/after" 2]

/-- clause 1 -/
def branchClause1 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .eq "resource/field/0/delta" 0,
    Pred.all [
      .eq "joint/index/1/cell/parent" p.VERDICTS,
      .eq "joint/index/1/cell/law" p.VERDICT_LAW,
      .eq "joint/index/1/resource/field/1/after" 2,
      .eqSlots "joint/index/1/resource/field/0/after" "resource/field/0/after",
      .eqSlots "joint/index/1/resource/field/4/after" "joint/index/2/cited/digest"]]

/-- clause 2 -/
def branchClause2 (p : Params) : Pred :=
  Pred.any [
    .not (.eq "request/verb" 2),
    .eq "resource/field/0/delta" 0,
    .eqSlots "resource/field/1/after" "joint/index/1/cell/id"]


end Law

def verdictClauses (p : Params) : List Pred :=
  [verdictClause0 p, verdictClause1 p, verdictClause2 p, verdictClause3 p, verdictClause4 p]

def verdictLaw (p : Params) : Pred := Pred.all (verdictClauses p)

def branchClauses (p : Params) : List Pred := [branchClause1 p, branchClause2 p]

def branchLaw (p : Params) : Pred := Pred.all (branchClauses p)

/-! ## §3. Law-level consequences -/

variable {o n : State}

theorem ev_writeOnce {s : String} :
    eval (.writeOnce s) o n = true ↔ ∀ x, o.get s = some x → x = 0 ∨ n.get s = some x := by
  simp only [eval, Minidregg.Pred.evalWith]
  cases o.get s <;> simp

/-- **Signer = producer.** Every admitted write of a verdict is signed by the subject its
`producer` field names after the write. -/
theorem verdict_signed_by_producer (p : Params) (admitted : eval (verdictLaw p) o n = true)
    (verb : n.get "request/verb" = some 2) :
    ∃ x, n.get "request/subject" = some x ∧ n.get "resource/field/3/after" = some x := by
  have c := ev_all.mp admitted (verdictClause1 p) (by simp [verdictClauses])
  simp only [verdictClause1, ev_any, ev_not, ev_eq, ev_eqSlots, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left] at c
  rcases c with c | c
  · exact absurd verb c
  · exact c

/-- **Written once.** A result that was written (present and not 0) is the result after every
admitted write. The same holds of each other field by the same clause. -/
theorem verdict_written_once (p : Params) (admitted : eval (verdictLaw p) o n = true)
    (verb : n.get "request/verb" = some 2) (r : Int)
    (was : o.get "resource/field/1/after" = some r) (written : r ≠ 0) :
    n.get "resource/field/1/after" = some r := by
  have c := ev_all.mp admitted (verdictClause2 p) (by simp [verdictClauses])
  simp only [verdictClause2, ev_any, ev_all, ev_not, ev_eq, ev_writeOnce, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq] at c
  rcases c with c | ⟨-, c, -⟩
  · exact absurd verb c
  · exact (c r was).resolve_left written

/-- **A result needs a red control.** After an admitted write, a verdict whose result is not
`unread` (1) records control `red` (2). -/
theorem verdict_result_needs_red_control (p : Params) (admitted : eval (verdictLaw p) o n = true)
    (verb : n.get "request/verb" = some 2) (read : n.get "resource/field/1/after" ≠ some 1) :
    n.get "resource/field/2/after" = some 2 := by
  have c := ev_all.mp admitted (verdictClause4 p) (by simp [verdictClauses])
  simp only [verdictClause4, ev_any, ev_not, ev_eq, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left] at c
  rcases c with c | c | c
  · exact absurd verb c
  · exact absurd c read
  · exact c

/-- **A land needs a current passing verdict.** An admitted write that moves the head cites at
position 1 a cell born under the verdict room and committed to the verdict law, whose result is
`pass`, whose tree is the new head, and whose read set is the digest of the footprint cited at
position 2. The first two are the controller's record of the cell, not its fields. -/
theorem land_needs_current_passing_verdict (p : Params) (admitted : eval (branchLaw p) o n = true)
    (verb : n.get "request/verb" = some 2) (moved : n.get "resource/field/0/delta" ≠ some 0) :
    n.get "joint/index/1/cell/parent" = some p.VERDICTS ∧
      n.get "joint/index/1/cell/law" = some p.VERDICT_LAW ∧
      n.get "joint/index/1/resource/field/1/after" = some 2 ∧
      (∃ x, n.get "joint/index/1/resource/field/0/after" = some x ∧
        n.get "resource/field/0/after" = some x) ∧
      (∃ d, n.get "joint/index/1/resource/field/4/after" = some d ∧
        n.get "joint/index/2/cited/digest" = some d) := by
  have c := ev_all.mp admitted (branchClause1 p) (by simp [branchClauses])
  simp only [branchClause1, ev_any, ev_all, ev_not, ev_eq, ev_eqSlots, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq] at c
  rcases c with c | c | c
  · exact absurd verb c
  · exact absurd c moved
  · exact c

/-- **Teeth.** A head move is refused when the cell at position 1 was born elsewhere, is under
another law, or is not a pass, whatever else the step holds. -/
theorem land_refused (p : Params) (verb : n.get "request/verb" = some 2)
    (moved : n.get "resource/field/0/delta" ≠ some 0)
    (bad : n.get "joint/index/1/cell/parent" ≠ some p.VERDICTS ∨
      n.get "joint/index/1/cell/law" ≠ some p.VERDICT_LAW ∨
      n.get "joint/index/1/resource/field/1/after" ≠ some 2) :
    eval (branchLaw p) o n = false := by
  rw [Bool.eq_false_iff]
  intro admitted
  obtain ⟨parent, law, result, -, -⟩ := land_needs_current_passing_verdict p admitted verb moved
  rcases bad with h | h | h
  · exact h parent
  · exact h law
  · exact h result

/-! ## §4. The footprint, on `citedRead` -/

/-- The digest a law reads at a cited position is the digest of the reads the turn cited. -/
theorem cited_digest_slot (id : Nat) (reads : List FieldRead) (store : Store effectLayout) :
    ("cited/digest", Int.ofNat (citedDigest reads).value) ∈ citedProject id reads store := by
  unfold citedProject
  exact List.mem_append_right _ (List.Mem.tail _ (List.Mem.head _))

/-- A cited read of an object cell whose keys are its own fields and whose grant names them is
decided by the moved fields alone. -/
theorem citedRead_decided (snapshot : AuthoritySnapshot) (id : Nat) (capability : CapabilityId)
    (reads : List FieldRead) (store : Store effectLayout)
    (keys : (reads.all fun read =>
      DeclaredActionLowering.writableKeyCheck (⟨id⟩ : ResourceId .object) read.1) = true)
    (granted : citedScope snapshot .object capability reads = none) :
    citedRead snapshot .object id capability 1 (some capability) false reads store =
      if citedMoved store reads = [] then .ok store
      else .error (.citedStale (citedMoved store reads)) := by
  unfold citedRead
  simp [keys, granted]

/-- The cell a verdict was computed over. -/
def base : Nat := 5

def field (number : Nat) : StateKey := .objectField ⟨base⟩ ⟨number⟩

/-- The footprint the verdict recorded: fields 0 and 1 of the base cell and the values read. -/
def footprint : List FieldRead := [(field 0, some 11), (field 1, some 22)]

/-- The base cell as the verdict read it; field 2 is not cited. -/
def read0 : Store effectLayout :=
  (((0 : Store effectLayout).set (field 0).address (some 11)).set (field 1).address (some 22)).set
    (field 2).address (some 33)

/-- Both cited fields moved. -/
def movedBoth : Store effectLayout :=
  (read0.set (field 0).address (some 12)).set (field 1).address (some 23)

/-- One cited field moved. -/
def movedOne : Store effectLayout := read0.set (field 1).address (some 23)

/-- Both cited fields back at the cited values; the uncited field differs from `read0`. -/
def movedBack : Store effectLayout :=
  ((movedBoth.set (field 0).address (some 11)).set (field 1).address (some 22)).set
    (field 2).address (some 99)

theorem field_ne {a b : Nat} (differ : a ≠ b) : (field a).address ≠ (field b).address := by
  intro same
  have := StateKey.address_injective same
  simp only [field, StateKey.objectField.injEq, Digest.mk.injEq, true_and] at this
  exact differ this

theorem moved_read0 : citedMoved read0 footprint = [] := by
  simp [citedMoved, footprint, read0, Store.set_ne _ _ _ _ (field_ne (a := 0) (b := 1) (by decide)),
    Store.set_ne _ _ _ _ (field_ne (a := 0) (b := 2) (by decide)),
    Store.set_ne _ _ _ _ (field_ne (a := 1) (b := 2) (by decide))]

theorem moved_movedBoth : citedMoved movedBoth footprint = [field 0, field 1] := by
  simp [citedMoved, footprint, movedBoth,
    Store.set_ne _ _ _ _ (field_ne (a := 0) (b := 1) (by decide))]

theorem moved_movedOne : citedMoved movedOne footprint = [field 1] := by
  simp [citedMoved, footprint, movedOne, read0,
    Store.set_ne _ _ _ _ (field_ne (a := 0) (b := 1) (by decide)),
    Store.set_ne _ _ _ _ (field_ne (a := 0) (b := 2) (by decide))]

theorem moved_movedBack : citedMoved movedBack footprint = [] := by
  simp [citedMoved, footprint, movedBack,
    Store.set_ne _ _ _ _ (field_ne (a := 0) (b := 1) (by decide)),
    Store.set_ne _ _ _ _ (field_ne (a := 0) (b := 2) (by decide)),
    Store.set_ne _ _ _ _ (field_ne (a := 1) (b := 2) (by decide))]

theorem movedBack_ne_read0 : movedBack ≠ read0 := by
  intro same
  have at2 := congrArg (fun store : Store effectLayout => store (field 2).address) same
  simp [movedBack, read0] at at2

/-- **The land's footprint, start to finish.** With a grant that names the cited fields:
the read is admitted at the store the verdict read and returns it unchanged; after both cited
fields move it is refused naming both, and after one moves naming that one; after they move
back it is admitted again, at a store that is not the first one. No refusal carries a value. -/
theorem land_footprint_scenario (snapshot : AuthoritySnapshot) (capability : CapabilityId)
    (granted : citedScope snapshot .object capability footprint = none) :
    citedRead snapshot .object base capability 1 (some capability) false footprint read0 =
        .ok read0 ∧
      citedRead snapshot .object base capability 1 (some capability) false footprint movedBoth =
        .error (.citedStale [field 0, field 1]) ∧
      citedRead snapshot .object base capability 1 (some capability) false footprint movedOne =
        .error (.citedStale [field 1]) ∧
      citedRead snapshot .object base capability 1 (some capability) false footprint movedBack =
        .ok movedBack ∧
      movedBack ≠ read0 := by
  have keys : (footprint.all fun read =>
      DeclaredActionLowering.writableKeyCheck (⟨base⟩ : ResourceId .object) read.1) = true := by
    decide
  refine ⟨?_, ?_, ?_, ?_, movedBack_ne_read0⟩
  · rw [citedRead_decided snapshot base capability footprint _ keys granted, moved_read0]; rfl
  · rw [citedRead_decided snapshot base capability footprint _ keys granted, moved_movedBoth]; rfl
  · rw [citedRead_decided snapshot base capability footprint _ keys granted, moved_movedOne]; rfl
  · rw [citedRead_decided snapshot base capability footprint _ keys granted, moved_movedBack]; rfl

/-! ## §5. Poles on concrete steps, by `decide` -/

def fleet : Params := { VERDICTS := 60, VERDICT_LAW := 4242 }

/-- A verdict as a step sees it after a write by `subject`. -/
def verdictStep (subject tree result control producer readset : Int) : State :=
  ⟨[("request/verb", 2), ("request/subject", subject), ("resource/field/0/after", tree),
    ("resource/field/1/after", result), ("resource/field/2/after", control),
    ("resource/field/3/after", producer), ("resource/field/4/after", readset)]⟩

set_option maxRecDepth 20000 in
/-- **The verdict law's poles.** Born passing with a red control, by its producer: admitted. A
pass with no red control, a pass signed by another subject, a result rewritten from pass to
fail, and a re-law attempt (verb 4) are refused. Born unread with no control: admitted. -/
theorem verdict_poles :
    eval (verdictLaw fleet) ⟨[]⟩ (verdictStep 7 77 2 2 7 9001) = true ∧
      eval (verdictLaw fleet) ⟨[]⟩ (verdictStep 7 77 2 1 7 9001) = false ∧
      eval (verdictLaw fleet) ⟨[]⟩ (verdictStep 8 77 2 2 7 9001) = false ∧
      eval (verdictLaw fleet) (verdictStep 7 77 2 2 7 9001) (verdictStep 7 77 3 2 7 9001) = false ∧
      eval (verdictLaw fleet) ⟨[]⟩ ⟨[("request/verb", 4), ("request/subject", 7)]⟩ = false ∧
      eval (verdictLaw fleet) ⟨[]⟩ (verdictStep 7 77 1 1 7 9001) = true := by
  decide

/-- A land as the branch's step sees it: the head written to `head`, the controller's record of
the cell at position 1, the three fields cited from it, and the digest of the footprint cited at
position 2. -/
def landStep (head parent law tree result readset digest : Int) : State :=
  ⟨[("request/verb", 2), ("resource/field/0/after", head), ("resource/field/0/delta", 1),
    ("resource/field/1/after", 9), ("joint/index/1/cell/id", 9),
    ("joint/index/1/cell/parent", parent), ("joint/index/1/cell/law", law),
    ("joint/index/1/resource/field/0/after", tree), ("joint/index/1/resource/field/1/after", result),
    ("joint/index/1/resource/field/4/after", readset), ("joint/index/2/cited/digest", digest)]⟩

set_option maxRecDepth 20000 in
/-- **The branch law's poles.** A land citing a passing verdict for the new head, born under the
verdict room (60) under the verdict law (4242), with the verdict's read set equal to the cited
footprint's digest: admitted. Refused: a look-alike born elsewhere (61); a cell under another
law; a verdict for another tree; an unread and a failing verdict; a footprint other than the one
the verdict recorded. -/
theorem land_poles :
    eval (branchLaw fleet) ⟨[]⟩ (landStep 77 60 4242 77 2 9001 9001) = true ∧
      eval (branchLaw fleet) ⟨[]⟩ (landStep 77 61 4242 77 2 9001 9001) = false ∧
      eval (branchLaw fleet) ⟨[]⟩ (landStep 77 60 4243 77 2 9001 9001) = false ∧
      eval (branchLaw fleet) ⟨[]⟩ (landStep 77 60 4242 78 2 9001 9001) = false ∧
      eval (branchLaw fleet) ⟨[]⟩ (landStep 77 60 4242 77 1 9001 9001) = false ∧
      eval (branchLaw fleet) ⟨[]⟩ (landStep 77 60 4242 77 3 9001 9001) = false ∧
      eval (branchLaw fleet) ⟨[]⟩ (landStep 77 60 4242 77 2 9001 9002) = false := by
  decide

#assert_axioms verdict_signed_by_producer verdict_written_once verdict_result_needs_red_control
  land_needs_current_passing_verdict land_refused cited_digest_slot citedRead_decided
  land_footprint_scenario verdict_poles land_poles

end Minidregg.Assurance.CitedLand
