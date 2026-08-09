/-
# Theory.PrivateComputationDeclaration — typed private-computation authority

The three private-computation families share one semantic declaration shape but
remain distinct in the type index.  Cryptographic execution is represented only
by abstract Lean evidence portals with data witnesses and explicit acceptance
laws.  A completion token conjoins every authority leg; it is not a receipt
codec and contains no runtime callback surface.
-/
import Theory.DisclosureDeclaration

namespace Minidregg.Theory

/-- The supported semantic families.  No constructor coerces evidence or
artifacts between families. -/
inductive PrivateComputationKind
  | witnessZk
  | sharedMpc
  | encryptedRnsFhe
  deriving DecidableEq, Repr

/-- A request must say whether output is ordinarily revealed or exceptionally
declassified.  Declassification carries its authority as first-order data. -/
inductive DisclosureIntent (DeclassificationAuthority : Type*)
  | reveal
  | declassify (authority : DeclassificationAuthority)
  deriving DecidableEq, Repr

/-- The committed effect materialized by an outcome. -/
inductive DisclosureEffect (DeclassificationAuthority Release : Type*)
  | reveal (release : Release)
  | declassify (authority : DeclassificationAuthority) (release : Release)
  deriving DecidableEq, Repr

def DisclosureIntent.materialize
    {DeclassificationAuthority Release : Type*}
    (intent : DisclosureIntent DeclassificationAuthority) (release : Release) :
    DisclosureEffect DeclassificationAuthority Release :=
  match intent with
  | .reveal => .reveal release
  | .declassify authority => .declassify authority release

/-- Mode-indexed program, artifact, and evidence families.  A ZK witness cannot
inhabit an MPC request, and an MPC transcript cannot inhabit an FHE request. -/
structure PrivateComputationLanguage where
  Program : PrivateComputationKind → Type
  InputArtifact : PrivateComputationKind → Type
  OutputArtifact : PrivateComputationKind → Type
  Evidence : PrivateComputationKind → Type

/-- The exact computation request.  It carries the semantic input as well as
the canonical and mode-native representations which must be joined. -/
structure PrivateComputationRequest
    (language : PrivateComputationLanguage) (mode : PrivateComputationKind)
    (Observer Policy Recipient Purpose BridgeName AuthorizationContext
      CanonicalInput SemanticInput DeclassificationAuthority : Type*) where
  authorizationContext : AuthorizationContext
  program : language.Program mode
  canonicalInput : CanonicalInput
  computationInput : language.InputArtifact mode
  inputValue : SemanticInput
  inputBridgeName : BridgeName
  disclosureRequest : DisclosureRequest Observer Policy Recipient Purpose
  disclosureIntent : DisclosureIntent DeclassificationAuthority

/-- A private outcome keeps the semantic output available to Lean while the
public commitment and mode-native representation remain explicit artifacts. -/
structure PrivateComputationOutcome
    (language : PrivateComputationLanguage) (mode : PrivateComputationKind)
    (OutputCommitment PrivateOutput DeclassificationAuthority Release : Type*) where
  output : CommittedPrivateOutput OutputCommitment (language.OutputArtifact mode) PrivateOutput
  evidence : language.Evidence mode
  release : Release
  disclosureEffect : DisclosureEffect DeclassificationAuthority Release

/-- The exact statement supplied to a mode-specific evidence portal. -/
structure PrivateComputationStatement
    (language : PrivateComputationLanguage) (mode : PrivateComputationKind)
    (SemanticInput OutputCommitment PrivateOutput : Type*) where
  program : language.Program mode
  inputValue : SemanticInput
  inputArtifact : language.InputArtifact mode
  outputCommitment : OutputCommitment
  outputArtifact : language.OutputArtifact mode
  privateOutput : PrivateOutput

/-- An abstract evidence portal.  `Witness` is ordinary Lean data.  The law is
explicit: verifier acceptance establishes exactly `Accepts statement witness`.
It makes no claim about an unmodeled implementation. -/
structure PrivateEvidencePortal (Statement Witness : Type*) where
  verify : Statement → Witness → Bool
  Accepts : Statement → Witness → Prop
  accepted_law : ∀ statement witness, verify statement witness = true →
    Accepts statement witness

/-- Proof-relevant use of an evidence portal. -/
structure CheckedPrivateEvidence
    {Statement Witness : Type*} (portal : PrivateEvidencePortal Statement Witness)
    (statement : Statement) where
  witness : Witness
  verified : portal.verify statement witness = true

theorem CheckedPrivateEvidence.accepts
    {Statement Witness : Type*} {portal : PrivateEvidencePortal Statement Witness}
    {statement : Statement} (checked : CheckedPrivateEvidence portal statement) :
    portal.Accepts statement checked.witness :=
  portal.accepted_law statement checked.witness checked.verified

/-- The only representation bridge shape.  Every bridge has a first-order name;
there is no unnamed/raw cross-representation constructor. -/
structure NamedRepresentationBridge
    (BridgeName SourceArtifact SourceWitness TargetArtifact TargetWitness Value : Type*) where
  name : BridgeName
  verifySource : SourceArtifact → SourceWitness → Value → Bool
  verifyTarget : TargetArtifact → TargetWitness → Value → Bool

namespace NamedRepresentationBridge

variable
    {BridgeName SourceArtifact SourceWitness TargetArtifact TargetWitness Value : Type*}
    (bridge : NamedRepresentationBridge BridgeName SourceArtifact SourceWitness
      TargetArtifact TargetWitness Value)

def sourceSemantics : OpeningSemantics SourceArtifact SourceWitness Value where
  opens artifact witness value := bridge.verifySource artifact witness value = true

def targetSemantics : OpeningSemantics TargetArtifact TargetWitness Value where
  opens artifact witness value := bridge.verifyTarget artifact witness value = true

def verifyIdentity (source : SourceArtifact) (sourceWitness : SourceWitness)
    (target : TargetArtifact) (targetWitness : TargetWitness) (value : Value) : Bool :=
  bridge.verifySource source sourceWitness value &&
    bridge.verifyTarget target targetWitness value

/-- A bridge check is indexed by the declared name and exact artifacts/value. -/
structure CheckedIdentity
    (declaredName : BridgeName) (source : SourceArtifact) (target : TargetArtifact)
    (value : Value) where
  nameBound : declaredName = bridge.name
  sourceWitness : SourceWitness
  targetWitness : TargetWitness
  verified : bridge.verifyIdentity source sourceWitness target targetWitness value = true

theorem CheckedIdentity.sameOpening
    {declaredName : BridgeName} {source : SourceArtifact} {target : TargetArtifact}
    {value : Value} (checked : bridge.CheckedIdentity declaredName source target value) :
    SameOpening bridge.sourceSemantics bridge.targetSemantics
      source checked.sourceWitness target checked.targetWitness := by
  have checks :
      bridge.verifySource source checked.sourceWitness value = true ∧
        bridge.verifyTarget target checked.targetWitness value = true := by
    simpa only [verifyIdentity, Bool.and_eq_true] using checked.verified
  exact ⟨value, checks.1, checks.2⟩

end NamedRepresentationBridge

/-- One mode-specific authored declaration.  Authorization sees the entire
request.  Computation evidence sees the exact request-derived statement. -/
structure PrivateComputationDeclaration
    (language : PrivateComputationLanguage) (mode : PrivateComputationKind)
    (Observer Policy Recipient Purpose BridgeName AuthorizationContext
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      AuthorizationWitness OutputCommitment PrivateOutput OutputSourceWitness
      OutputTargetWitness ReleaseAuthorizationWitness DeclassificationAuthority Release : Type*) where
  authorizationPortal : PrivateEvidencePortal
    (PrivateComputationRequest language mode Observer Policy Recipient Purpose BridgeName
      AuthorizationContext CanonicalInput SemanticInput DeclassificationAuthority)
    AuthorizationWitness
  inputBridge : NamedRepresentationBridge BridgeName CanonicalInput InputSourceWitness
    (language.InputArtifact mode) InputTargetWitness SemanticInput
  computationPortal : PrivateEvidencePortal
    (PrivateComputationStatement language mode SemanticInput OutputCommitment PrivateOutput)
    (language.Evidence mode)
  disclosureDeclaration : DisclosureDeclaration Observer Policy Recipient Purpose
    OutputCommitment (language.OutputArtifact mode) PrivateOutput OutputSourceWitness
    OutputTargetWitness ReleaseAuthorizationWitness Release

namespace PrivateComputationDeclaration

variable
    {language : PrivateComputationLanguage} {mode : PrivateComputationKind}
    {Observer Policy Recipient Purpose BridgeName AuthorizationContext
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      AuthorizationWitness OutputCommitment PrivateOutput OutputSourceWitness
      OutputTargetWitness ReleaseAuthorizationWitness DeclassificationAuthority Release : Type*}
    (declaration : PrivateComputationDeclaration language mode Observer Policy Recipient Purpose
      BridgeName AuthorizationContext CanonicalInput SemanticInput InputSourceWitness
      InputTargetWitness AuthorizationWitness OutputCommitment PrivateOutput OutputSourceWitness
      OutputTargetWitness ReleaseAuthorizationWitness DeclassificationAuthority Release)

abbrev Request :=
  PrivateComputationRequest language mode Observer Policy Recipient Purpose BridgeName
    AuthorizationContext CanonicalInput SemanticInput DeclassificationAuthority

abbrev Outcome :=
  PrivateComputationOutcome language mode OutputCommitment PrivateOutput
    DeclassificationAuthority Release

def statementOf (request : declaration.Request) (outcome : declaration.Outcome) :
    PrivateComputationStatement language mode SemanticInput OutputCommitment PrivateOutput where
  program := request.program
  inputValue := request.inputValue
  inputArtifact := request.computationInput
  outputCommitment := outcome.output.commitment
  outputArtifact := outcome.output.representation
  privateOutput := outcome.output.privateOutput

/-- The completion token.  Every field is proof-relevant and indexed by the
same request/outcome; no constructor permits authorization, input identity,
computation evidence, or declared disclosure to be omitted. -/
structure Completion [DecidableEq Release]
    (request : declaration.Request) (outcome : declaration.Outcome) where
  authorization : CheckedPrivateEvidence declaration.authorizationPortal request
  inputIdentity : declaration.inputBridge.CheckedIdentity request.inputBridgeName
    request.canonicalInput request.computationInput request.inputValue
  computation : CheckedPrivateEvidence declaration.computationPortal
    (declaration.statementOf request outcome)
  outputDisclosure : declaration.disclosureDeclaration.VerifiedRelease
    request.disclosureRequest outcome.output outcome.release
  disclosureDeclared :
    outcome.disclosureEffect = request.disclosureIntent.materialize outcome.release

/-- Completion exposes all semantic authority legs.  The two representation
joins are existing `SameOpening` relations and the output policy judgment is the
existing `AuthorizedRelease`; portal conclusions follow only through their
explicit acceptance laws. -/
theorem Completion.implies_declared_semantics [DecidableEq Release]
    {request : declaration.Request} {outcome : declaration.Outcome}
    (completion : declaration.Completion request outcome) :
    declaration.authorizationPortal.Accepts request completion.authorization.witness ∧
      SameOpening declaration.inputBridge.sourceSemantics
        declaration.inputBridge.targetSemantics
        request.canonicalInput completion.inputIdentity.sourceWitness
        request.computationInput completion.inputIdentity.targetWitness ∧
      declaration.computationPortal.Accepts
        (declaration.statementOf request outcome) completion.computation.witness ∧
      outcome.disclosureEffect = request.disclosureIntent.materialize outcome.release ∧
      (SameOpening
          declaration.disclosureDeclaration.sourceOpeningSemantics
          declaration.disclosureDeclaration.targetOpeningSemantics
          outcome.output.commitment
          completion.outputDisclosure.sameOpening.witness.source
          outcome.output.representation
          completion.outputDisclosure.sameOpening.witness.target ∧
        AuthorizedRelease declaration.disclosureDeclaration.releaseSemantics
          request.disclosureRequest request.disclosureRequest.recipient
          request.disclosureRequest.purpose outcome.output.privateOutput outcome.release) := by
  have outputRelations := completion.outputDisclosure.implies_privacy_relations
  exact ⟨completion.authorization.accepts,
    completion.inputIdentity.sameOpening,
    completion.computation.accepts,
    completion.disclosureDeclared,
    outputRelations⟩

end PrivateComputationDeclaration

end Minidregg.Theory
