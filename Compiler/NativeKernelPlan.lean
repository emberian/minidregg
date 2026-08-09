/-
# Compiler.NativeKernelPlan — Lean-owned plans for opaque native work

This module exposes a closed, first-order work vocabulary.  A plan instruction
can name arithmetic, hash, or transform work, but it has no accept/reject,
policy, continuation, or callback field.  Its semantic payload is an existing
`BignumKernelABI.KernelCall`: despite that historical module name, the call has
one generic descriptor entry and its relation is exactly `descriptorHolds`.

The opaque boundary returns either an opaque native error or a fixed-width field
buffer.  An error blocks the plan before any certificate or continuation.  Lean checks the
manifest clause registration, ABI shape, public-input prefix, and emitted
descriptor before it invokes the runner on the next instruction.  Consequently
the runner neither chooses the continuation nor constructs the sole `Verified`
token.

`arbitraryRunner_integrity` assumes nothing about the runner.  Reaching
`Verified` exposes, for every plan instruction, its registered manifest clause,
well-formed generated call, exact public prefix, and existing descriptor
acceptance.  This is a control-integrity theorem, not a native semantics or a
native-refinement theorem.
-/
import Compiler.BignumKernelABI
import Compiler.SemanticManifest

namespace Minidregg.Compiler.NativeKernelPlan

open Minidregg.Compiler
open Minidregg.Compiler.BignumKernelABI
open Minidregg.Compiler.SemanticManifest
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## 1. Closed first-order plan surface -/

/-- The complete native work vocabulary.  These are work classifications, not
semantic decisions. -/
inductive WorkKind
  | arithmetic
  | hash
  | transform
deriving DecidableEq, Repr

/-- One generated instruction.

* `clauseId` is interpreted only through `SemanticManifest.lookupClause`;
* `call` reuses the generic, emitted-descriptor ABI;
* `publicInputs` is a first-order list whose exact length is checked by Lean.

There is no policy, acceptance bit, rejection code, or continuation here. -/
structure Instruction where
  kind : WorkKind
  clauseId : Digest
  call : KernelCall
  publicInputs : List BabyBear

/-- A generated plan carries the canonical first-order manifest value and fixes
instruction order as first-order list data.  Executable control compares this
structure directly; it never normalizes the theorem-oriented Gödel
`Manifest.contentAddress`.  A deployment hash may authenticate the serialized
payload outside this relation. -/
structure Plan where
  manifestEncoding : ManifestEncoding
  instructions : List Instruction

/-- Convenience constructors preserve the closed work vocabulary.  Hash and
transform meaning still comes from the supplied Lean-emitted descriptor and
registered manifest clause, not from these labels. -/
def Instruction.arithmetic (clauseId : Digest) (call : KernelCall)
    (publicInputs : List BabyBear) : Instruction :=
  ⟨.arithmetic, clauseId, call, publicInputs⟩

def Instruction.hash (clauseId : Digest) (call : KernelCall)
    (publicInputs : List BabyBear) : Instruction :=
  ⟨.hash, clauseId, call, publicInputs⟩

def Instruction.transform (clauseId : Digest) (call : KernelCall)
    (publicInputs : List BabyBear) : Instruction :=
  ⟨.transform, clauseId, call, publicInputs⟩

/-! ## 2. Bounded response data and opaque runner -/

/-- Native output is exactly the generated descriptor's finite wire buffer.
There is no Boolean, proposition, acceptance constructor, or continuation. -/
structure KernelResponse (instruction : Instruction) where
  wires : Fin instruction.call.descriptor.nWires → BabyBear

/-- Extend the bounded buffer only for consumption by the existing descriptor
relation.  Indices outside the declared response width read as zero. -/
def KernelResponse.totalWires {instruction : Instruction}
    (response : KernelResponse instruction) : Nat → BabyBear := fun index =>
  if h : index < instruction.call.descriptor.nWires then
    response.wires ⟨index, h⟩
  else 0

/-- The only opaque boundary.  A runner receives one Lean-selected instruction
and returns either an opaque error or its bounded data response.  Neither branch
contains acceptance, policy, or a continuation. -/
abbrev PlanRunner (Error : Type) :=
  (instruction : Instruction) → Except Error (KernelResponse instruction)

/-! ## 3. Lean-owned checks and certificates -/

/-! ### Finite executable reflection of the existing propositions -/

def dWireBoundedCheck (bound : Nat) : DWire BabyBear → Bool
  | .cnst _ => true
  | .wire index => decide (index < bound)

@[simp] theorem dWireBoundedCheck_eq_true_iff
    (bound : Nat) (wire : DWire BabyBear) :
    dWireBoundedCheck bound wire = true ↔ wire.bounded bound := by
  cases wire <;> simp [dWireBoundedCheck, DWire.bounded]

def dGateInBoundsCheck (descriptor : ConstraintDescriptor BabyBear)
    (gate : DGate BabyBear) : Bool :=
  dWireBoundedCheck descriptor.nWires gate.a &&
  dWireBoundedCheck descriptor.nWires gate.b &&
  decide (descriptor.nVars ≤ gate.out) &&
  decide (gate.out < descriptor.nWires)

@[simp] theorem dGateInBoundsCheck_eq_true_iff
    (descriptor : ConstraintDescriptor BabyBear) (gate : DGate BabyBear) :
    dGateInBoundsCheck descriptor gate = true ↔
      gate.a.bounded descriptor.nWires ∧
      gate.b.bounded descriptor.nWires ∧
      descriptor.nVars ≤ gate.out ∧ gate.out < descriptor.nWires := by
  simp [dGateInBoundsCheck, and_assoc]

def descriptorWellFormedCheck
    (descriptor : ConstraintDescriptor BabyBear) : Bool :=
  decide (descriptor.nPublic ≤ descriptor.nVars) &&
  decide (descriptor.nVars ≤ descriptor.nWires) &&
  descriptor.gates.all (dGateInBoundsCheck descriptor) &&
  descriptor.zeros.all (dWireBoundedCheck descriptor.nWires)

theorem descriptorWellFormedCheck_eq_true_iff
    (descriptor : ConstraintDescriptor BabyBear) :
    descriptorWellFormedCheck descriptor = true ↔ descriptor.WellFormed := by
  simp only [descriptorWellFormedCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, dGateInBoundsCheck_eq_true_iff,
    dWireBoundedCheck_eq_true_iff]
  constructor
  · rintro ⟨⟨⟨publicLe, varsLe⟩, gatesIn⟩, zerosIn⟩
    exact ⟨publicLe, varsLe, gatesIn, zerosIn⟩
  · rintro ⟨publicLe, varsLe, gatesIn, zerosIn⟩
    exact ⟨⟨⟨publicLe, varsLe⟩, gatesIn⟩, zerosIn⟩

def visibilityFitsCheck (nPublic : Nat) (segment : WireSegment) : Bool :=
  match segment.visibility with
  | .publicInput => decide (segment.offset + segment.length ≤ nPublic)
  | .witness => decide (nPublic ≤ segment.offset)

@[simp] theorem visibilityFitsCheck_eq_true_iff
    (nPublic : Nat) (segment : WireSegment) :
    visibilityFitsCheck nPublic segment = true ↔
      segment.visibilityFits nPublic := by
  cases h : segment.visibility <;>
    simp [visibilityFitsCheck, WireSegment.visibilityFits, h]

def segmentsCoverFromCheck (nPublic : Nat) :
    Nat → List WireSegment → Nat → Bool
  | cursor, [], nVars => decide (cursor = nVars)
  | cursor, segment :: rest, nVars =>
      decide (segment.offset = cursor) &&
      decide (segment.offset + segment.length ≤ nVars) &&
      visibilityFitsCheck nPublic segment &&
      segmentsCoverFromCheck nPublic
        (segment.offset + segment.length) rest nVars

theorem segmentsCoverFromCheck_eq_true_iff (nPublic cursor nVars : Nat)
    (segments : List WireSegment) :
    segmentsCoverFromCheck nPublic cursor segments nVars = true ↔
      segmentsCoverFrom nPublic cursor segments nVars := by
  induction segments generalizing cursor with
  | nil => simp [segmentsCoverFromCheck, segmentsCoverFrom]
  | cons segment rest ih =>
      simp [segmentsCoverFromCheck, segmentsCoverFrom, ih, and_assoc]

def spanInBoundsCheck (nVars : Nat) (span : WireSpan) : Bool :=
  decide (span.start + span.length ≤ nVars)

@[simp] theorem spanInBoundsCheck_eq_true_iff
    (nVars : Nat) (span : WireSpan) :
    spanInBoundsCheck nVars span = true ↔ span.inBounds nVars := by
  simp [spanInBoundsCheck, WireSpan.inBounds]

def addWellShapedCheck (nVars : Nat) (call : AddCall) : Bool :=
  decide (call.x.length = call.width) &&
  decide (call.y.length = call.width) &&
  decide (call.z.length = call.width) &&
  decide (call.xBits.length = call.width * call.limbBits) &&
  decide (call.yBits.length = call.width * call.limbBits) &&
  decide (call.zBits.length = call.width * call.limbBits) &&
  decide (call.carry.length = call.width + 1) &&
  [call.x, call.y, call.z, call.xBits, call.yBits, call.zBits, call.carry].all
    (spanInBoundsCheck nVars)

theorem addWellShapedCheck_eq_true_iff (nVars : Nat) (call : AddCall) :
    addWellShapedCheck nVars call = true ↔ call.WellShaped nVars := by
  simp [addWellShapedCheck, AddCall.WellShaped, and_assoc]

def scalarMulConstWellShapedCheck
    (nVars : Nat) (call : ScalarMulConstCall) : Bool :=
  decide (call.scalar.length = 1) &&
  decide (call.scalarBits.length = call.quotientBits) &&
  decide (call.product.length = call.width) &&
  decide (call.productBits.length = call.width * call.limbBits) &&
  decide (call.carry.length = call.width + 1) &&
  decide (call.carryBits.length = (call.width + 1) * call.quotientBits) &&
  [call.scalar, call.scalarBits, call.product, call.productBits,
    call.carry, call.carryBits].all (spanInBoundsCheck nVars)

theorem scalarMulConstWellShapedCheck_eq_true_iff
    (nVars : Nat) (call : ScalarMulConstCall) :
    scalarMulConstWellShapedCheck nVars call = true ↔
      call.WellShaped nVars := by
  simp [scalarMulConstWellShapedCheck, ScalarMulConstCall.WellShaped,
    and_assoc]

def witnessCallWellShapedCheck (nVars : Nat) : WitnessCall → Bool
  | .add call => addWellShapedCheck nVars call
  | .scalarMulConst call => scalarMulConstWellShapedCheck nVars call

@[simp] theorem witnessCallWellShapedCheck_eq_true_iff
    (nVars : Nat) (call : WitnessCall) :
    witnessCallWellShapedCheck nVars call = true ↔
      call.WellShaped nVars := by
  cases call <;> simp [witnessCallWellShapedCheck, WitnessCall.WellShaped,
    addWellShapedCheck_eq_true_iff, scalarMulConstWellShapedCheck_eq_true_iff]

def kernelCallFullyWellFormedCheck (call : KernelCall) : Bool :=
  descriptorWellFormedCheck call.descriptor &&
  segmentsCoverFromCheck call.descriptor.nPublic 0 call.segments
    call.descriptor.nVars &&
  call.calls.all (witnessCallWellShapedCheck call.descriptor.nVars)

theorem kernelCallFullyWellFormedCheck_eq_true_iff (call : KernelCall) :
    kernelCallFullyWellFormedCheck call = true ↔ call.FullyWellFormed := by
  simp only [kernelCallFullyWellFormedCheck, Bool.and_eq_true,
    descriptorWellFormedCheck_eq_true_iff,
    segmentsCoverFromCheck_eq_true_iff, List.all_eq_true,
    witnessCallWellShapedCheck_eq_true_iff]
  constructor
  · rintro ⟨⟨descriptor, layout⟩, calls⟩
    exact ⟨⟨descriptor, layout⟩, calls⟩
  · rintro ⟨⟨descriptor, layout⟩, calls⟩
    exact ⟨⟨descriptor, layout⟩, calls⟩

def finAll (n : Nat) (check : Fin n → Bool) : Bool :=
  (List.finRange n).all check

@[simp] theorem finAll_eq_true_iff (n : Nat) (check : Fin n → Bool) :
    finAll n check = true ↔ ∀ index, check index = true := by
  simp [finAll]

def descriptorHoldsCheck (descriptor : ConstraintDescriptor BabyBear)
    (wireValues : Nat → BabyBear) : Bool :=
  (descriptor.gates.all fun gate =>
    decide (gate.op.denote (gate.a.read wireValues) (gate.b.read wireValues) =
      wireValues gate.out)) &&
  descriptor.zeros.all fun zero => decide (zero.read wireValues = 0)

theorem descriptorHoldsCheck_eq_true_iff
    (descriptor : ConstraintDescriptor BabyBear)
    (wireValues : Nat → BabyBear) :
    descriptorHoldsCheck descriptor wireValues = true ↔
      descriptorHolds descriptor wireValues := by
  simp [descriptorHoldsCheck, descriptorHolds, DGate.holds]

/-- Public inputs are bound positionally to the descriptor's public prefix.
The separate length equality prevents a short list from being padded with the
`getD` default. -/
def PublicPrefixExact (instruction : Instruction)
    (response : KernelResponse instruction) : Prop :=
  instruction.publicInputs.length = instruction.call.descriptor.nPublic ∧
  ∀ index : Fin instruction.call.descriptor.nPublic,
    response.totalWires index.val =
      instruction.publicInputs.getD index.val 0

def publicPrefixExactCheck (instruction : Instruction)
    (response : KernelResponse instruction) : Bool :=
  decide
    (instruction.publicInputs.length = instruction.call.descriptor.nPublic) &&
  finAll instruction.call.descriptor.nPublic fun index =>
    decide (response.totalWires index.val =
      instruction.publicInputs.getD index.val 0)

theorem publicPrefixExactCheck_eq_true_iff (instruction : Instruction)
    (response : KernelResponse instruction) :
    publicPrefixExactCheck instruction response = true ↔
      PublicPrefixExact instruction response := by
  simp [publicPrefixExactCheck, PublicPrefixExact]

def kernelCallAcceptsCheck (instruction : Instruction)
    (response : KernelResponse instruction) : Bool :=
  descriptorHoldsCheck instruction.call.descriptor response.totalWires

theorem kernelCallAcceptsCheck_eq_true_iff (instruction : Instruction)
    (response : KernelResponse instruction) :
    kernelCallAcceptsCheck instruction response = true ↔
      instruction.call.Accepts response.totalWires := by
  exact descriptorHoldsCheck_eq_true_iff _ _

/-- Everything Lean certifies before it advances past one instruction.  The
arithmetic/hash/transform labels add no parallel semantics: acceptance is the
existing generic call relation. -/
structure CertifiedResponse (manifest : Manifest) (instruction : Instruction)
    (response : KernelResponse instruction) : Type where
  clauseRegistered :
    ∃ clause : DialectClauseDecl,
      manifest.lookupClause instruction.clauseId = some clause
  callWellFormed : instruction.call.FullyWellFormed
  publicPrefixExact : PublicPrefixExact instruction response
  descriptorAcceptance : instruction.call.Accepts response.totalWires

/-- Proof that Lean checked every response in the plan's fixed order.  Each node
stores the exact bounded response and its runner-return equation; later proofs
never call the opaque runner again to recover certificate data. -/
inductive Certificate (manifest : Manifest) {Error : Type}
    (runner : PlanRunner Error) :
    List Instruction → Type
  | nil : Certificate manifest runner []
  | cons {instruction : Instruction} {rest : List Instruction}
      (response : KernelResponse instruction)
      (returned : runner instruction = .ok response)
      (head : CertifiedResponse manifest instruction response)
      (tail : Certificate manifest runner rest) :
      Certificate manifest runner (instruction :: rest)

inductive Failure
  | manifestEncodingMismatch
  | unregisteredClause (clauseId : Digest)
  | malformedCall (clauseId : Digest)
  | publicPrefixMismatch (clauseId : Digest)
  | descriptorRejected (clauseId : Digest)
deriving DecidableEq, Repr

/-- Internal result for a suffix.  Native errors block before continuation;
Lean-check failures reject; only Lean constructs the checked certificate. -/
inductive SuffixOutcome (Error : Type) (manifest : Manifest)
    (runner : PlanRunner Error)
    (instructions : List Instruction)
  | blocked (error : Error)
  | rejected (failure : Failure)
  | checked (certificate : Certificate manifest runner instructions)

/-- Lean checker for one response.  Clause lookup is performed before the
descriptor checks, so no unregistered native work can reach the continuation. -/
def checkInstruction (manifest : Manifest) (instruction : Instruction)
    (response : KernelResponse instruction) :
    Sum Failure (CertifiedResponse manifest instruction response) := by
  match hclause : manifest.lookupClause instruction.clauseId with
  | none => exact .inl (.unregisteredClause instruction.clauseId)
  | some clause =>
      if hcallCheck : kernelCallFullyWellFormedCheck instruction.call = true then
        if hprefixCheck : publicPrefixExactCheck instruction response = true then
          if hacceptsCheck : kernelCallAcceptsCheck instruction response = true then
            exact .inr
              { clauseRegistered := ⟨clause, hclause⟩
                callWellFormed :=
                  (kernelCallFullyWellFormedCheck_eq_true_iff _).mp hcallCheck
                publicPrefixExact :=
                  (publicPrefixExactCheck_eq_true_iff _ _).mp hprefixCheck
                descriptorAcceptance :=
                  (kernelCallAcceptsCheck_eq_true_iff _ _).mp hacceptsCheck }
          else exact .inl (.descriptorRejected instruction.clauseId)
        else exact .inl (.publicPrefixMismatch instruction.clauseId)
      else exact .inl (.malformedCall instruction.clauseId)

/-- Execute and check instructions in Lean-owned order.  The recursive call—and
therefore the next native invocation—exists only in the certified branch. -/
def checkInstructions {Error : Type} (manifest : Manifest)
    (runner : PlanRunner Error) :
    (instructions : List Instruction) →
      SuffixOutcome Error manifest runner instructions
  | [] => .checked .nil
  | instruction :: rest =>
      match hreturned : runner instruction with
      | .error error => .blocked error
      | .ok response =>
          match checkInstruction manifest instruction response with
          | .inl failure => .rejected failure
          | .inr head =>
              match checkInstructions manifest runner rest with
              | .blocked error => .blocked error
              | .rejected failure => .rejected failure
              | .checked tail =>
                  .checked (.cons response hreturned head tail)

/-- A native error at the head instruction blocks before the Lean checker and
before the recursive continuation.  It cannot be encoded as a response buffer. -/
theorem checkInstructions_headError {Error : Type}
    (manifest : Manifest) (runner : PlanRunner Error)
    (instruction : Instruction) (rest : List Instruction) (error : Error)
    (failed : runner instruction = .error error) :
    checkInstructions manifest runner (instruction :: rest) = .blocked error := by
  unfold checkInstructions
  split
  · rename_i returnedError returned
    have same : returnedError = error := by
      have equality := returned.symm.trans failed
      exact Except.error.inj equality
    subst returnedError
    rfl
  · rename_i response returned
    have impossible := returned.symm.trans failed
    cases impossible

/-! ## 4. Sole verified token and controller run -/

/-- The only successful controller token. -/
structure Verified (manifest : Manifest) (plan : Plan)
    {Error : Type} (runner : PlanRunner Error) : Type where
  manifestExact : plan.manifestEncoding = manifest.canonicalEncoding
  certificate : Certificate manifest runner plan.instructions

inductive Outcome (Error : Type) (manifest : Manifest) (plan : Plan)
    (runner : PlanRunner Error)
  | blocked (error : Error)
  | rejected (failure : Failure)
  | verified (token : Verified manifest plan runner)

def Outcome.IsVerified {Error : Type} {manifest : Manifest} {plan : Plan}
    {runner : PlanRunner Error} : Outcome Error manifest plan runner → Prop
  | .blocked _ => False
  | .rejected _ => False
  | .verified _ => True

/-- Run the plan.  Manifest binding is checked before any native instruction is
issued; all later continuation choices remain inside `checkInstructions`. -/
def run {Error : Type} (manifest : Manifest) (plan : Plan)
    (runner : PlanRunner Error) : Outcome Error manifest plan runner :=
  if hmanifest : plan.manifestEncoding = manifest.canonicalEncoding then
    match checkInstructions manifest runner plan.instructions with
    | .blocked error => .blocked error
    | .rejected failure => .rejected failure
    | .checked certificate => .verified ⟨hmanifest, certificate⟩
  else .rejected .manifestEncodingMismatch

/-- If the first scheduled native instruction errors, the whole plan is
blocked with that exact error.  No check, certificate, or tail instruction is
reachable from this branch. -/
theorem firstInstructionError_blocks {Error : Type}
    (manifest : Manifest) (plan : Plan) (runner : PlanRunner Error)
    (instruction : Instruction) (rest : List Instruction) (error : Error)
    (manifestExact : plan.manifestEncoding = manifest.canonicalEncoding)
    (instructionsExact : plan.instructions = instruction :: rest)
    (failed : runner instruction = .error error) :
    run manifest plan runner = .blocked error := by
  cases plan with
  | mk encoding instructions =>
      dsimp only [Plan.instructions] at instructionsExact
      subst instructions
      unfold run
      split
      · rw [checkInstructions_headError manifest runner instruction rest error failed]
      · rename_i mismatch
        exact (mismatch manifestExact).elim

/-! ## 5. Arbitrary-runner integrity and teeth -/

theorem Certificate.checked_of_mem
    {Error : Type} {manifest : Manifest} {runner : PlanRunner Error}
    {instructions : List Instruction}
    (certificate : Certificate manifest runner instructions)
    {instruction : Instruction} (member : instruction ∈ instructions) :
    ∃ response : KernelResponse instruction,
      runner instruction = .ok response ∧
      Nonempty (CertifiedResponse manifest instruction response) := by
  induction certificate with
  | nil => simp at member
  | @cons headInstruction rest response returned head tail ih =>
      rcases List.mem_cons.mp member with same | member
      · subst instruction
        exact ⟨response, returned, ⟨head⟩⟩
      · exact ih member

/-- **Arbitrary-runner integrity.**  No honesty, determinism theorem, or native
semantics is assumed for `runner`.  If Lean reaches `Verified`, every instruction
has an exact registered clause and satisfies the existing descriptor relation on
the exact bounded response whose public prefix is plan-authored. -/
theorem arbitraryRunner_integrity
    {Error : Type} (manifest : Manifest) (plan : Plan)
    (runner : PlanRunner Error)
    (reached : (run manifest plan runner).IsVerified) :
    plan.manifestEncoding = manifest.canonicalEncoding ∧
    ∀ instruction, instruction ∈ plan.instructions →
      ∃ response : KernelResponse instruction,
        runner instruction = .ok response ∧
        ∃ clause : DialectClauseDecl,
          manifest.lookupClause instruction.clauseId = some clause ∧
          instruction.call.FullyWellFormed ∧
          PublicPrefixExact instruction response ∧
          instruction.call.Accepts response.totalWires := by
  cases hrun : run manifest plan runner with
  | blocked error =>
      rw [hrun] at reached
      exact False.elim reached
  | rejected failure =>
      rw [hrun] at reached
      exact False.elim reached
  | verified token =>
      refine ⟨token.manifestExact, ?_⟩
      intro instruction member
      rcases token.certificate.checked_of_mem member with
        ⟨response, returned, ⟨checked⟩⟩
      rcases checked.clauseRegistered with ⟨clause, registered⟩
      exact ⟨response, returned, clause, registered,
        checked.callWellFormed, checked.publicPrefixExact,
        checked.descriptorAcceptance⟩

/-- A response failing the emitted descriptor cannot be certified, regardless
of which work label or registered clause the instruction names. -/
theorem descriptorFailure_not_certified
    (manifest : Manifest) (instruction : Instruction)
    (response : KernelResponse instruction)
    (failure : ¬ instruction.call.Accepts response.totalWires) :
    ∀ certificate,
      checkInstruction manifest instruction response ≠ .inr certificate := by
  intro certificate _
  exact failure certificate.descriptorAcceptance

/-- A plan with the wrong canonical manifest never invokes the success branch. -/
theorem manifestMismatch_not_verified
    {Error : Type} (manifest : Manifest) (plan : Plan)
    (runner : PlanRunner Error)
    (mismatch : plan.manifestEncoding ≠ manifest.canonicalEncoding) :
    ¬ (run manifest plan runner).IsVerified := by
  intro reached
  unfold run at reached
  split at reached
  · rename_i same
    exact (mismatch same).elim
  · exact reached

#print axioms arbitraryRunner_integrity
#print axioms descriptorFailure_not_certified
#print axioms manifestMismatch_not_verified
#print axioms checkInstructions_headError
#print axioms firstInstructionError_blocks

end Minidregg.Compiler.NativeKernelPlan
