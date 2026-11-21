/-
# Kernel.BranchAdmission -- one branch of a birth: its evidence and its law's judgement

A birth is admitted branch by branch (factory, authority, each allocation, each Book source,
and for a grain-backed birth each grain target). Every branch runs the same two steps on the
old authority snapshot:

1. **Evidence** (`evidence`): the capability the credential names, checked against the
   request (`ComposedPolicyAdmission.Config.capabilityEvidenceChecked`), or the creator's
   signature at the current key epoch. `Mode` says which a branch takes.
2. **Judgement** (`judge`): the policy epoch and revision are current, the target's law
   resolves, the request binds to it, the compiler's three verdicts hold on the branch's step,
   and then the law's own verdict (`law.admit`).

`admit` is the two in order. The plain birth (`ResourceBirthPolicyController.Concrete.Pending.admitBranch`)
and the grain-backed birth (`GrainResourceBirthAdmission.Pending.admitBranch`) both call it and
map `Reject` into their own refusals; neither keeps a copy.

`judge_policyRejected` and `admit_policyRejected` say where `policyRejected` comes from: only
from a resolved law that fails `planVerdict` on the branch's step.
-/
module

public import Compiler.CredentialAuthorityPolicyRegistry
public import Compiler.PhysicalLawResolution
public import Theory.AssertAxioms

import all Init.Control.Except

@[expose] public section

namespace Minidregg.Kernel.BranchAdmission

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.LawComposition
open Minidregg.Theory.CellRegistry
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.PolicyComponentResolution
open Minidregg.Kernel.CanonicalPolicyRegistry

set_option autoImplicit false

/-- Which evidence a branch takes. -/
inductive Mode where
  /-- The branch presents a capability; none is refused `capability`. -/
  | required
  /-- A capability when the credential names one, else the creator's signature. -/
  | optional
  /-- The creator's signature only; a named capability is refused `credentialShape`. -/
  | forbidden
  deriving DecidableEq, Repr

inductive Reject where
  | capability
  | signature
  | credentialShape
  | policyUnavailable
  /-- The request does not bind to the resolved law (`ComposedPolicyAdmission.bind`). -/
  | policyBinding
  /-- The compiler cannot lower the resolved law (`supported`). -/
  | policyUnsupported
  /-- An input the law reads on the step is out of the compiler's range (`inputsInRange`). -/
  | policyInputRange
  /-- Two integers of the step share one field image (`castInjOn`). -/
  | policyCastAlias
  /-- The law evaluates false on the step, binding, support, range and cast having passed. -/
  | policyRejected
  deriving DecidableEq, Repr

variable {F : Type} [Field F] [DecidableEq F]

/-- The plan verdict on one resolved law: the compiler lowers it (`supported`), every input
it reads on the configuration's step is in range (`inputsInRange`), the step's integers cast
injectively (`castInjOn`), and the law evaluates true on that step. These are the checks
`judge` makes after binding, in its order; the last is the law's own verdict. -/
def planVerdict {config : ComposedPolicyAdmission.Config F}
    (law : ComposedPolicyAdmission.PreparedLaw config) : Bool :=
  Minidregg.Compiler.supported config.profile.compiler law.predicate &&
  Minidregg.Compiler.inputsInRange config.profile.compiler law.predicate
    config.step.oldState config.step.newState &&
  decide (Minidregg.Compiler.castInjOn F
    (Minidregg.Compiler.intsOf law.predicate config.step.oldState config.step.newState)) &&
  Minidregg.Pred.eval law.predicate config.step.oldState config.step.newState

/-- A branch's policy judgement, after its capability or signature evidence: epoch and
revision current, the law resolved, the request bound to it (`ComposedPolicyAdmission.bind`,
refused as `policyBinding`), the compiler's three verdicts on the configuration's step
(refused as `policyUnsupported`, `policyInputRange`, `policyCastAlias`), and only then the
law's own verdict through `law.admit` (refused as `policyRejected`). The authorization is
`law.admit`'s, unchanged. -/
def judge (config : ComposedPolicyAdmission.Config F) {kind : ResourceKind}
    (request : Request kind)
    (evidence : Evidence config.portal config.snapshot.authState request) :
    Except Reject (Authorized config.portal config.snapshot.authState request) :=
  let old := config.snapshot.authState
  if epoch : request.policyEpoch = old.policyEpoch request.policyId then
    if revision : request.policyRevision = old.policyRevision request.policyId then
      match config.resolve? with
      | none => .error .policyUnavailable
      | some law =>
          match ComposedPolicyAdmission.bind config request evidence law
              (.policy request.policyId request.policyRevision) epoch revision with
          | none => .error .policyBinding
          | some _ =>
            if Minidregg.Compiler.supported config.profile.compiler law.predicate = false then
              .error .policyUnsupported
            else if Minidregg.Compiler.inputsInRange config.profile.compiler law.predicate
                config.step.oldState config.step.newState = false then
              .error .policyInputRange
            else if ¬ Minidregg.Compiler.castInjOn F (Minidregg.Compiler.intsOf law.predicate
                config.step.oldState config.step.newState) then
              .error .policyCastAlias
            else
              match law.admit request evidence law.witness
                  (.policy request.policyId request.policyRevision) epoch revision with
              | none => .error .policyRejected
              | some admitted => .ok admitted
    else .error .policyUnavailable
  else .error .policyUnavailable

/-- **A bound request under the compiler's three verdicts is admitted when its law
evaluates true** on the configuration's step: `law.admit` on the law's own witness then
answers `some`. -/
theorem admit_some_of_bind {config : ComposedPolicyAdmission.Config F}
    {kind : ResourceKind} {request : Request kind}
    {evidence : Evidence config.portal config.snapshot.authState request}
    {law : ComposedPolicyAdmission.PreparedLaw config} {membership : config.portal.MembershipWitness}
    {epochExact : request.policyEpoch = config.snapshot.authState.policyEpoch request.policyId}
    {revisionExact : request.policyRevision =
      config.snapshot.authState.policyRevision request.policyId}
    {bound : ComposedPolicyAdmission.Bound config request}
    (bindExact : ComposedPolicyAdmission.bind config request evidence law membership
      epochExact revisionExact = some bound)
    (supportedExact : Minidregg.Compiler.supported config.profile.compiler law.predicate = true)
    (rangesExact : Minidregg.Compiler.inputsInRange config.profile.compiler law.predicate
      config.step.oldState config.step.newState = true)
    (casts : Minidregg.Compiler.castInjOn F
      (Minidregg.Compiler.intsOf law.predicate config.step.oldState config.step.newState))
    (evaluated : Minidregg.Pred.eval law.predicate config.step.oldState config.step.newState = true) :
    ∃ authorized, law.admit request evidence law.witness membership epochExact revisionExact =
      some authorized := by
  unfold ComposedPolicyAdmission.bind at bindExact
  split at bindExact
  next binding =>
    split at bindExact
    next addressExact =>
      split at bindExact
      next membershipVerified =>
        have verified := (ComposedPolicyAdmission.Bound.verifies_iff_eval
          (⟨evidence, law, binding, membership, epochExact, revisionExact, addressExact,
            membershipVerified⟩ : ComposedPolicyAdmission.Bound config request)
          supportedExact rangesExact casts).2 evaluated
        obtain ⟨authorized, admitted⟩ := ComposedPolicyAdmission.Bound.admit_of_verifies
          (⟨evidence, law, binding, membership, epochExact, revisionExact, addressExact,
            membershipVerified⟩ : ComposedPolicyAdmission.Bound config request) verified
        exact ⟨authorized, (ComposedPolicyAdmission.PreparedLaw.admit_eq law request evidence
          law.witness membership epochExact revisionExact).trans admitted⟩
      next => cases bindExact
    next => cases bindExact
  next => cases bindExact

/-- **`judge` refuses as `policyRejected` only on a law that fails the plan verdict**: the
law resolved, and (binding, support, range and cast having passed) it evaluates false on
the configuration's step. -/
theorem judge_policyRejected (config : ComposedPolicyAdmission.Config F) {kind : ResourceKind}
    (request : Request kind)
    (evidence : Evidence config.portal config.snapshot.authState request)
    (rejected : judge config request evidence = .error .policyRejected) :
    ∃ law : ComposedPolicyAdmission.PreparedLaw config,
      config.resolve? = some law ∧ planVerdict law = false := by
  unfold judge at rejected
  try dsimp only at rejected
  split at rejected
  next =>
    split at rejected
    next =>
      split at rejected
      next => cases rejected
      next law resolved =>
        refine ⟨law, resolved, ?_⟩
        split at rejected
        next => cases rejected
        next bound bindExact =>
          split at rejected
          next => cases rejected
          next unsupported =>
            split at rejected
            next => cases rejected
            next outOfRange =>
              split at rejected
              next => cases rejected
              next aliased =>
                split at rejected
                next refusedAdmit =>
                  cases evaluated : Minidregg.Pred.eval law.predicate
                      config.step.oldState config.step.newState
                  · simp only [planVerdict, evaluated, Bool.and_false]
                  · obtain ⟨authorized, admitted⟩ := admit_some_of_bind bindExact
                      (by simpa using unsupported) (by simpa using outOfRange)
                      (by simpa using aliased) evaluated
                    have contradiction := admitted.symm.trans refusedAdmit
                    cases contradiction
                next => cases rejected
    next => cases rejected
  next => cases rejected

/-- Teeth: a law that mentions `witnessed` (for instance `not (witnessed vk)`) is never judged
admitted. It is refused before the law is read (`policyUnavailable`, `policyBinding`) or,
past binding, by name as `policyUnsupported`. -/
theorem judge_witnessed (config : ComposedPolicyAdmission.Config F) {kind : ResourceKind}
    (request : Request kind)
    (evidence : Evidence config.portal config.snapshot.authState request)
    (law : ComposedPolicyAdmission.PreparedLaw config)
    (resolved : config.resolve? = some law)
    (witnessed : mentionsWitnessed law.predicate = true) :
    ∃ reason, judge config request evidence = .error reason ∧
      (reason = .policyUnavailable ∨ reason = .policyBinding ∨ reason = .policyUnsupported) := by
  unfold judge
  try dsimp only
  split
  next =>
    split
    next =>
      split
      next => exact ⟨_, rfl, .inl rfl⟩
      next resolvedLaw resolvedExact =>
        obtain rfl := Option.some.inj (resolved.symm.trans resolvedExact)
        split
        next => exact ⟨_, rfl, .inr (.inl rfl)⟩
        next =>
          rw [if_pos (unsupported_of_mentionsWitnessed config.profile.compiler witnessed)]
          exact ⟨_, rfl, .inr (.inr rfl)⟩
    next => exact ⟨_, rfl, .inl rfl⟩
  next => exact ⟨_, rfl, .inl rfl⟩

/-! ## Evidence over the source portal -/

/-- The configuration that judges `target`'s committed law on `step` at one loaded authority
snapshot, its evidence faces the source portal's under the use marker `marker`. -/
abbrev config (compiler : PolicyCompilerProfile F)
    (snapshot : CredentialAuthorityDomain.Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry) (marker : Nat)
    (step : PolicyStepContext) (target : Nat) (additional : List PolicyRef) :
    ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config compiler snapshot directory
    (CredentialAuthorityPolicyRegistry.sourcePortal snapshot marker) step target additional

/-- A branch's evidence: the named capability checked against the request, or the creator's
signature at the current key epoch, as `mode` allows. -/
def evidence (compiler : PolicyCompilerProfile F)
    (snapshot : CredentialAuthorityDomain.Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry) (marker : Nat)
    (step : PolicyStepContext) (target : Nat) (additional : List PolicyRef)
    {kind : ResourceKind} (request : Request kind) (mode : Mode)
    (capability : Option CapabilityId)
    (receipt : CredentialSignatureAdmission.CheckedSignature snapshot) :
    Except Reject (Evidence (config compiler snapshot directory marker step target additional).portal
      snapshot.authState request) :=
  let selected := config compiler snapshot directory marker step target additional
  let presented (identifier : CapabilityId) :
      Except Reject (Evidence selected.portal snapshot.authState request) :=
    match selected.capabilityEvidenceChecked request identifier () receipt () (fun _ => ()) with
    | .error _ => .error .capability
    | .ok evidence => .ok evidence
  let signed : Except Reject (Evidence selected.portal snapshot.authState request) :=
    if epoch : request.subjectKeyEpoch = snapshot.authState.subjectKeyEpoch request.subject then
      if verified : selected.portal.verifySignature request receipt = true then
        .ok (.signature receipt epoch verified)
      else .error .signature
    else .error .signature
  match mode, capability with
  | .required, none => .error .capability
  | .required, some identifier => presented identifier
  | .optional, some identifier => presented identifier
  | .optional, none => signed
  | .forbidden, some _ => .error .credentialShape
  | .forbidden, none => signed

/-- One branch: its evidence, then its law's judgement. -/
def admit (compiler : PolicyCompilerProfile F)
    (snapshot : CredentialAuthorityDomain.Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry) (marker : Nat)
    (step : PolicyStepContext) (target : Nat) (additional : List PolicyRef)
    {kind : ResourceKind} (request : Request kind) (mode : Mode)
    (capability : Option CapabilityId)
    (receipt : CredentialSignatureAdmission.CheckedSignature snapshot) :
    Except Reject (Authorized (config compiler snapshot directory marker step target additional).portal
      snapshot.authState request) :=
  match evidence compiler snapshot directory marker step target additional request mode
      capability receipt with
  | .error reason => .error reason
  | .ok presented =>
      judge (config compiler snapshot directory marker step target additional) request presented

/-- The evidence step never answers `policyRejected`. -/
theorem evidence_ne_policyRejected (compiler : PolicyCompilerProfile F)
    (snapshot : CredentialAuthorityDomain.Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry) (marker : Nat)
    (step : PolicyStepContext) (target : Nat) (additional : List PolicyRef)
    {kind : ResourceKind} (request : Request kind) (mode : Mode)
    (capability : Option CapabilityId)
    (receipt : CredentialSignatureAdmission.CheckedSignature snapshot) :
    evidence compiler snapshot directory marker step target additional request mode
      capability receipt ≠ .error .policyRejected := by
  intro refused
  unfold evidence at refused
  dsimp only at refused
  repeat' split at refused
  all_goals cases refused

/-- **`admit` answers `policyRejected` only from its policy judgement**, on some evidence the
branch presented. -/
theorem admit_policyRejected (compiler : PolicyCompilerProfile F)
    (snapshot : CredentialAuthorityDomain.Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry) (marker : Nat)
    (step : PolicyStepContext) (target : Nat) (additional : List PolicyRef)
    {kind : ResourceKind} (request : Request kind) (mode : Mode)
    (capability : Option CapabilityId)
    (receipt : CredentialSignatureAdmission.CheckedSignature snapshot)
    (rejected : admit compiler snapshot directory marker step target additional request mode
      capability receipt = .error .policyRejected) :
    ∃ presented, judge (config compiler snapshot directory marker step target additional)
      request presented = .error .policyRejected := by
  unfold admit at rejected
  split at rejected
  next reason refused =>
    injection rejected with same
    subst same
    exact absurd refused (evidence_ne_policyRejected compiler snapshot directory marker step
      target additional request mode capability receipt)
  next presented _ => exact ⟨presented, rejected⟩

/-- Satisfiable pole of the mode table: a required branch with no capability is refused
`capability` before any signature or law is read. -/
theorem evidence_required_none (compiler : PolicyCompilerProfile F)
    (snapshot : CredentialAuthorityDomain.Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry) (marker : Nat)
    (step : PolicyStepContext) (target : Nat) (additional : List PolicyRef)
    {kind : ResourceKind} (request : Request kind)
    (receipt : CredentialSignatureAdmission.CheckedSignature snapshot) :
    evidence compiler snapshot directory marker step target additional request .required
      none receipt = .error .capability := rfl

/-- A signature-only branch that names a capability is refused `credentialShape`. -/
theorem evidence_forbidden_some (compiler : PolicyCompilerProfile F)
    (snapshot : CredentialAuthorityDomain.Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry) (marker : Nat)
    (step : PolicyStepContext) (target : Nat) (additional : List PolicyRef)
    {kind : ResourceKind} (request : Request kind) (identifier : CapabilityId)
    (receipt : CredentialSignatureAdmission.CheckedSignature snapshot) :
    evidence compiler snapshot directory marker step target additional request .forbidden
      (some identifier) receipt = .error .credentialShape := rfl

#assert_axioms admit_some_of_bind
#assert_axioms judge_policyRejected
#assert_axioms judge_witnessed
#assert_axioms admit_policyRejected

end Minidregg.Kernel.BranchAdmission
