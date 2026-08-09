/-
# Compiler.NativeKernelPlan — Lean-owned plans for opaque native work

This module exposes a closed, first-order work vocabulary.  A plan instruction
can name arithmetic, hash, or transform work, but it has no accept/reject,
policy, continuation, or callback field.  Its semantic payload is an existing
`BignumKernelABI.KernelCall`: despite that historical module name, the call has
one generic descriptor entry and its relation is exactly `descriptorHolds`.

The opaque boundary returns only a fixed-width field buffer.  Lean checks the
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

/-- A generated plan binds its manifest content address and fixes instruction
order as first-order list data. -/
structure Plan where
  manifestAddress : Digest
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
and returns its bounded data response. -/
abbrev PlanRunner :=
  (instruction : Instruction) → KernelResponse instruction

/-! ## 3. Lean-owned checks and certificates -/

/-- Public inputs are bound positionally to the descriptor's public prefix.
The separate length equality prevents a short list from being padded with the
`getD` default. -/
def PublicPrefixExact (instruction : Instruction)
    (response : KernelResponse instruction) : Prop :=
  instruction.publicInputs.length = instruction.call.descriptor.nPublic ∧
  ∀ index : Fin instruction.call.descriptor.nPublic,
    response.totalWires index.val =
      instruction.publicInputs.getD index.val 0

/-- Everything Lean certifies before it advances past one instruction.  The
arithmetic/hash/transform labels add no parallel semantics: acceptance is the
existing generic call relation. -/
structure CertifiedResponse (manifest : Manifest) (instruction : Instruction)
    (response : KernelResponse instruction) : Prop where
  clause : NativeClauseDecl
  clauseRegistered :
    manifest.lookupClause instruction.clauseId = some clause
  callWellFormed : instruction.call.FullyWellFormed
  publicPrefixExact : PublicPrefixExact instruction response
  descriptorAcceptance : instruction.call.Accepts response.totalWires

/-- Proof that Lean checked every response in the plan's fixed order. -/
inductive Certificate (manifest : Manifest) (runner : PlanRunner) :
    List Instruction → Prop
  | nil : Certificate manifest runner []
  | cons {instruction : Instruction} {rest : List Instruction}
      (head : CertifiedResponse manifest instruction (runner instruction))
      (tail : Certificate manifest runner rest) :
      Certificate manifest runner (instruction :: rest)

inductive Failure
  | manifestAddressMismatch
  | unregisteredClause (clauseId : Digest)
  | malformedCall (clauseId : Digest)
  | publicPrefixMismatch (clauseId : Digest)
  | descriptorRejected (clauseId : Digest)
deriving DecidableEq, Repr

/-- Internal result for a suffix.  Only Lean constructs the certificate. -/
inductive SuffixOutcome (manifest : Manifest) (runner : PlanRunner)
    (instructions : List Instruction)
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
      if hcall : instruction.call.FullyWellFormed then
        if hprefix : PublicPrefixExact instruction response then
          if haccepts : instruction.call.Accepts response.totalWires then
            exact .inr
              { clause := clause
                clauseRegistered := hclause
                callWellFormed := hcall
                publicPrefixExact := hprefix
                descriptorAcceptance := haccepts }
          else exact .inl (.descriptorRejected instruction.clauseId)
        else exact .inl (.publicPrefixMismatch instruction.clauseId)
      else exact .inl (.malformedCall instruction.clauseId)

/-- Execute and check instructions in Lean-owned order.  The recursive call—and
therefore the next native invocation—exists only in the certified branch. -/
def checkInstructions (manifest : Manifest) (runner : PlanRunner) :
    (instructions : List Instruction) → SuffixOutcome manifest runner instructions
  | [] => .checked .nil
  | instruction :: rest =>
      match checkInstruction manifest instruction (runner instruction) with
      | .inl failure => .rejected failure
      | .inr head =>
          match checkInstructions manifest runner rest with
          | .rejected failure => .rejected failure
          | .checked tail => .checked (.cons head tail)

/-! ## 4. Sole verified token and controller run -/

/-- The only successful controller token. -/
structure Verified (manifest : Manifest) (plan : Plan)
    (runner : PlanRunner) : Prop where
  manifestExact : plan.manifestAddress = manifest.contentAddress
  certificate : Certificate manifest runner plan.instructions

inductive Outcome (manifest : Manifest) (plan : Plan) (runner : PlanRunner)
  | rejected (failure : Failure)
  | verified (token : Verified manifest plan runner)

def Outcome.IsVerified {manifest : Manifest} {plan : Plan}
    {runner : PlanRunner} : Outcome manifest plan runner → Prop
  | .rejected _ => False
  | .verified _ => True

/-- Run the plan.  Manifest binding is checked before any native instruction is
issued; all later continuation choices remain inside `checkInstructions`. -/
def run (manifest : Manifest) (plan : Plan) (runner : PlanRunner) :
    Outcome manifest plan runner :=
  if hmanifest : plan.manifestAddress = manifest.contentAddress then
    match checkInstructions manifest runner plan.instructions with
    | .rejected failure => .rejected failure
    | .checked certificate => .verified ⟨hmanifest, certificate⟩
  else .rejected .manifestAddressMismatch

/-! ## 5. Arbitrary-runner integrity and teeth -/

theorem Certificate.checked_of_mem
    {manifest : Manifest} {runner : PlanRunner}
    {instructions : List Instruction}
    (certificate : Certificate manifest runner instructions)
    {instruction : Instruction} (member : instruction ∈ instructions) :
    CertifiedResponse manifest instruction (runner instruction) := by
  induction certificate with
  | nil => simp at member
  | @cons headInstruction rest head tail ih =>
      rcases List.mem_cons.mp member with same | member
      · subst instruction
        exact head
      · exact ih member

/-- **Arbitrary-runner integrity.**  No honesty, determinism theorem, or native
semantics is assumed for `runner`.  If Lean reaches `Verified`, every instruction
has an exact registered clause and satisfies the existing descriptor relation on
the exact bounded response whose public prefix is plan-authored. -/
theorem arbitraryRunner_integrity
    (manifest : Manifest) (plan : Plan) (runner : PlanRunner)
    (reached : (run manifest plan runner).IsVerified) :
    plan.manifestAddress = manifest.contentAddress ∧
    ∀ instruction, instruction ∈ plan.instructions →
      ∃ clause : NativeClauseDecl,
        manifest.lookupClause instruction.clauseId = some clause ∧
        instruction.call.FullyWellFormed ∧
        PublicPrefixExact instruction (runner instruction) ∧
        instruction.call.Accepts (runner instruction).totalWires := by
  cases hrun : run manifest plan runner with
  | rejected failure => simp [Outcome.IsVerified, hrun] at reached
  | verified token =>
      refine ⟨token.manifestExact, ?_⟩
      intro instruction member
      have checked := token.certificate.checked_of_mem member
      exact ⟨checked.clause, checked.clauseRegistered,
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
  intro certificate
  simp [checkInstruction, failure]

/-- A plan with the wrong manifest address never invokes the success branch. -/
theorem manifestMismatch_not_verified
    (manifest : Manifest) (plan : Plan) (runner : PlanRunner)
    (mismatch : plan.manifestAddress ≠ manifest.contentAddress) :
    ¬ (run manifest plan runner).IsVerified := by
  simp [run, mismatch, Outcome.IsVerified]

#print axioms arbitraryRunner_integrity
#print axioms descriptorFailure_not_certified
#print axioms manifestMismatch_not_verified

end Minidregg.Compiler.NativeKernelPlan
