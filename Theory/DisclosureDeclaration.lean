/-
# Theory.DisclosureDeclaration — one authority for private-output release

The request and artifacts are first-order data.  A declaration owns the
executable checks and projection.  A `VerifiedRelease` retains evidence that
both the committed-output join and the exact request-indexed authorization
check accepted; neither check can be skipped by selecting another constructor.
-/
import Theory.IndexedProgram
import Theory.PrivacyProfile

namespace Minidregg.Theory

open IndexedProgram

/-- The complete first-order disclosure request.  In particular, the observer
is part of the request value checked by authorization, not ambient context. -/
structure DisclosureRequest (Observer Policy Recipient Purpose : Type*) where
  observer : Observer
  policy : Policy
  recipient : Recipient
  purpose : Purpose

/-- The semantic private output together with both public representations that
must be shown to open to it. -/
structure CommittedPrivateOutput
    (CommitmentArtifact OutputArtifact PrivateOutput : Type*) where
  commitment : CommitmentArtifact
  representation : OutputArtifact
  privateOutput : PrivateOutput

/-- A declaration is the single authored surface for one disclosure dialect.
Boundary data has lawful codecs; checks return `Bool` and receive the complete
request or actual committed output.  Their induced propositions below are
defined by verifier acceptance, so this layer asserts no cryptographic claim. -/
structure DisclosureDeclaration
    (Observer Policy Recipient Purpose CommitmentArtifact OutputArtifact PrivateOutput
      SourceWitness TargetWitness AuthorizationWitness Release : Type*) where
  requestCodec : LawfulCodec (DisclosureRequest Observer Policy Recipient Purpose)
  commitmentCodec : LawfulCodec CommitmentArtifact
  representationCodec : LawfulCodec OutputArtifact
  releaseCodec : LawfulCodec Release
  verifySourceOpening : CommitmentArtifact → SourceWitness → PrivateOutput → Bool
  verifyTargetOpening : OutputArtifact → TargetWitness → PrivateOutput → Bool
  verifyPermission :
    DisclosureRequest Observer Policy Recipient Purpose →
      PrivateOutput → AuthorizationWitness → Bool
  projectRelease :
    DisclosureRequest Observer Policy Recipient Purpose → PrivateOutput → Release

namespace DisclosureDeclaration

variable
    {Observer Policy Recipient Purpose CommitmentArtifact OutputArtifact PrivateOutput
      SourceWitness TargetWitness AuthorizationWitness Release : Type*}
    (declaration : DisclosureDeclaration Observer Policy Recipient Purpose CommitmentArtifact
      OutputArtifact PrivateOutput SourceWitness TargetWitness AuthorizationWitness Release)

/-- The source opening semantics induced by the declaration's executable check. -/
def sourceOpeningSemantics :
    OpeningSemantics CommitmentArtifact SourceWitness PrivateOutput where
  opens artifact witness output :=
    declaration.verifySourceOpening artifact witness output = true

/-- The target opening semantics induced by the declaration's executable check. -/
def targetOpeningSemantics :
    OpeningSemantics OutputArtifact TargetWitness PrivateOutput where
  opens artifact witness output :=
    declaration.verifyTargetOpening artifact witness output = true

/-- The existing `ReleaseSemantics`, specialized so its policy argument is the
whole disclosure request.  This preserves the observer and every policy index
when projecting to `AuthorizedRelease`. -/
def releaseSemantics :
    ReleaseSemantics
      (DisclosureRequest Observer Policy Recipient Purpose)
      Recipient Purpose PrivateOutput Release where
  permitted request recipient purpose output :=
    recipient = request.recipient ∧ purpose = request.purpose ∧
      ∃ witness, declaration.verifyPermission request output witness = true
  project request _recipient _purpose output :=
    declaration.projectRelease request output

/-- The private witnesses for the two representations.  Both checks are made
against `output.privateOutput`, so a witness cannot substitute another value. -/
structure SameOpeningWitness
    (output : CommittedPrivateOutput CommitmentArtifact OutputArtifact PrivateOutput) where
  source : SourceWitness
  target : TargetWitness

def verifySameOpening
    (output : CommittedPrivateOutput CommitmentArtifact OutputArtifact PrivateOutput)
    (witness : SameOpeningWitness (SourceWitness := SourceWitness)
      (TargetWitness := TargetWitness) output) : Bool :=
  declaration.verifySourceOpening output.commitment witness.source output.privateOutput &&
    declaration.verifyTargetOpening output.representation witness.target output.privateOutput

/-- Proof-relevant acceptance of the same-opening check. -/
structure CheckedSameOpening
    (output : CommittedPrivateOutput CommitmentArtifact OutputArtifact PrivateOutput) where
  witness : SameOpeningWitness (SourceWitness := SourceWitness)
    (TargetWitness := TargetWitness) output
  verified : verifySameOpening declaration output witness = true

/-- The authorization check is indexed by the exact request, output, and
released value.  It conjoins permission evidence with equality to the declared
projection. -/
def verifyAuthorization [DecidableEq Release]
    (request : DisclosureRequest Observer Policy Recipient Purpose)
    (output : CommittedPrivateOutput CommitmentArtifact OutputArtifact PrivateOutput)
    (release : Release) (witness : AuthorizationWitness) : Bool :=
  declaration.verifyPermission request output.privateOutput witness &&
    decide (release = declaration.projectRelease request output.privateOutput)

/-- Proof-relevant request-indexed authorization. -/
structure ReleaseAuthorization [DecidableEq Release]
    (request : DisclosureRequest Observer Policy Recipient Purpose)
    (output : CommittedPrivateOutput CommitmentArtifact OutputArtifact PrivateOutput)
    (release : Release) where
  witness : AuthorizationWitness
  verified : verifyAuthorization declaration request output release witness = true

/-- The only accepted release shape: both checks are fields, and authorization
is indexed by the same request/output/release carried by this type. -/
structure VerifiedRelease [DecidableEq Release]
    (request : DisclosureRequest Observer Policy Recipient Purpose)
    (output : CommittedPrivateOutput CommitmentArtifact OutputArtifact PrivateOutput)
    (release : Release) where
  sameOpening : declaration.CheckedSameOpening output
  authorization : declaration.ReleaseAuthorization request output release

/-- Untrusted candidate material.  Construction confers no authority. -/
structure ReleaseCandidate
    (request : DisclosureRequest Observer Policy Recipient Purpose)
    (output : CommittedPrivateOutput CommitmentArtifact OutputArtifact PrivateOutput)
    (release : Release) where
  sameOpeningWitness : SameOpeningWitness (SourceWitness := SourceWitness)
    (TargetWitness := TargetWitness) output
  authorizationWitness : AuthorizationWitness

def verifyCandidate [DecidableEq Release]
    {request : DisclosureRequest Observer Policy Recipient Purpose}
    {output : CommittedPrivateOutput CommitmentArtifact OutputArtifact PrivateOutput}
    {release : Release}
    (candidate : ReleaseCandidate (SourceWitness := SourceWitness)
      (TargetWitness := TargetWitness) (AuthorizationWitness := AuthorizationWitness)
      request output release) : Bool :=
  verifySameOpening declaration output candidate.sameOpeningWitness &&
    verifyAuthorization declaration request output release candidate.authorizationWitness

/-- Executable, fail-closed construction.  `none` is returned unless both
checks accept; the resulting type retains the two acceptance equalities. -/
def accept [DecidableEq Release]
    {request : DisclosureRequest Observer Policy Recipient Purpose}
    {output : CommittedPrivateOutput CommitmentArtifact OutputArtifact PrivateOutput}
    {release : Release}
    (candidate : ReleaseCandidate (SourceWitness := SourceWitness)
      (TargetWitness := TargetWitness) (AuthorizationWitness := AuthorizationWitness)
      request output release) :
    Option (declaration.VerifiedRelease request output release) :=
  if accepted : verifyCandidate declaration candidate = true then
    have checks :
        verifySameOpening declaration output candidate.sameOpeningWitness = true ∧
          verifyAuthorization declaration request output release
            candidate.authorizationWitness = true := by
      simpa only [verifyCandidate, Bool.and_eq_true] using accepted
    some {
      sameOpening := {
        witness := candidate.sameOpeningWitness
        verified := checks.1
      }
      authorization := {
        witness := candidate.authorizationWitness
        verified := checks.2
      }
    }
  else
    none

/-- Acceptance exposes exactly the two existing `PrivacyProfile` relations: the
two artifacts have one common opening (the actual private output), and the
release is authorized by the complete request. -/
theorem VerifiedRelease.implies_privacy_relations [DecidableEq Release]
    {request : DisclosureRequest Observer Policy Recipient Purpose}
    {output : CommittedPrivateOutput CommitmentArtifact OutputArtifact PrivateOutput}
    {release : Release}
    (verified : declaration.VerifiedRelease request output release) :
    SameOpening (sourceOpeningSemantics declaration) (targetOpeningSemantics declaration)
        output.commitment verified.sameOpening.witness.source
        output.representation verified.sameOpening.witness.target ∧
      AuthorizedRelease (releaseSemantics declaration) request request.recipient request.purpose
        output.privateOutput release := by
  have openingChecks :
      declaration.verifySourceOpening output.commitment
          verified.sameOpening.witness.source output.privateOutput = true ∧
        declaration.verifyTargetOpening output.representation
          verified.sameOpening.witness.target output.privateOutput = true := by
    simpa only [verifySameOpening, Bool.and_eq_true] using verified.sameOpening.verified
  have authorizationChecks :
      declaration.verifyPermission request output.privateOutput
          verified.authorization.witness = true ∧
        decide (release = declaration.projectRelease request output.privateOutput) = true := by
    simpa only [verifyAuthorization, Bool.and_eq_true] using verified.authorization.verified
  have releaseBound :
      release = declaration.projectRelease request output.privateOutput := by
    simpa only [decide_eq_true_eq] using authorizationChecks.2
  refine ⟨?_, ?_⟩
  · exact ⟨output.privateOutput, openingChecks.1, openingChecks.2⟩
  · refine ⟨?_, releaseBound⟩
    exact ⟨rfl, rfl, verified.authorization.witness, authorizationChecks.1⟩

/-! ## Indexed declaration program -/

inductive DeclarationPhase
  | pending
  | decided
  deriving DecidableEq, Repr

/-- One first-order declaration operation.  Its response selects the terminal
typestate, so downstream interpretations cannot observe a pre-check release. -/
inductive DeclarationOp : DeclarationPhase → Type _
  | verify
      {request : DisclosureRequest Observer Policy Recipient Purpose}
      {output : CommittedPrivateOutput CommitmentArtifact OutputArtifact PrivateOutput}
      {release : Release}
      (candidate : ReleaseCandidate (SourceWitness := SourceWitness)
        (TargetWitness := TargetWitness) (AuthorizationWitness := AuthorizationWitness)
        request output release) :
      DeclarationOp .pending

def signature [DecidableEq Release] : IxSignature DeclarationPhase :=
  let _declarationMarker := declaration
  {
    Op := DeclarationOp (Observer := Observer) (Policy := Policy) (Recipient := Recipient)
      (Purpose := Purpose) (CommitmentArtifact := CommitmentArtifact)
      (OutputArtifact := OutputArtifact) (PrivateOutput := PrivateOutput)
      (SourceWitness := SourceWitness) (TargetWitness := TargetWitness)
      (AuthorizationWitness := AuthorizationWitness) (Release := Release)
    Resp := fun
      | .verify _ => Bool
    next := fun
      | .verify _, _ => .decided
  }

def DeclarationResult : DeclarationPhase → Type
  | .pending => PEmpty
  | .decided => Bool

/-- The syntax tree is derived from the declaration operation rather than a
second verifier language. -/
def program [DecidableEq Release]
    {request : DisclosureRequest Observer Policy Recipient Purpose}
    {output : CommittedPrivateOutput CommitmentArtifact OutputArtifact PrivateOutput}
    {release : Release}
    (candidate : ReleaseCandidate (SourceWitness := SourceWitness)
      (TargetWitness := TargetWitness) (AuthorizationWitness := AuthorizationWitness)
      request output release) :
    Program declaration.signature DeclarationResult .pending :=
  .call (.verify candidate) fun accepted => .pure accepted

def handler [DecidableEq Release] :
    Handler declaration.signature (fun _ => Unit) where
  handle := fun
    | .verify candidate, _ => ⟨declaration.verifyCandidate candidate, ()⟩

/-- The indexed interpreter executes exactly the same declaration check. -/
theorem interpret_program [DecidableEq Release]
    {request : DisclosureRequest Observer Policy Recipient Purpose}
    {output : CommittedPrivateOutput CommitmentArtifact OutputArtifact PrivateOutput}
    {release : Release}
    (candidate : ReleaseCandidate (SourceWitness := SourceWitness)
      (TargetWitness := TargetWitness) (AuthorizationWitness := AuthorizationWitness)
      request output release) :
    interpret declaration.handler (declaration.program candidate) () =
      (⟨.decided, (declaration.verifyCandidate candidate, ())⟩ :
        Outcome DeclarationResult (fun _ => Unit)) :=
  rfl

end DisclosureDeclaration

end Minidregg.Theory
