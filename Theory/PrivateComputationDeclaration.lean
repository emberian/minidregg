/-
# Theory.PrivateComputationDeclaration — typed private-computation authority

The three private-computation families share one semantic declaration shape but
remain distinct in the type index.  Cryptographic execution is represented only
by abstract Lean evidence portals with data witnesses and explicit acceptance
laws.  Computation completion is separate from release completion; neither is
a receipt codec or runtime callback surface.
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

/-! ## Release-free computation core -/

/-- The exact canonical footprint named by a computation request.  It is data,
not a claim that a candidate patch respects it; the kernel adapter below checks
that the accepted patch has these exact two footprints. -/
structure ComputationFootprint (Field Resource : Type*) where
  fields : Finset Field
  resources : Finset Resource

/-- First-order syntax for sealed computation.  This is the authoritative
request shape for witness-ZK, shared-MPC, and encrypted-RNS/FHE work.

There is deliberately no observer, disclosure policy, recipient, purpose,
release value, reveal bit, or declassification authority in this structure.
The output commitment and typed resource effects describe what the computation
may produce; disclosure of that committed output is a separate later request. -/
structure CoreRequest
    (language : PrivateComputationLanguage) (mode : PrivateComputationKind)
    (Relation BridgeName CanonicalInput SemanticInput
      OutputCommitment ResourceEffect Footprint Nullifier
      ModeEvidencePins : Type*) where
  program : language.Program mode
  relation : Relation
  canonicalInput : CanonicalInput
  computationInput : language.InputArtifact mode
  inputValue : SemanticInput
  inputBridgeName : BridgeName
  outputCommitment : OutputCommitment
  resourceEffects : List ResourceEffect
  footprint : Footprint
  nullifier : Option Nullifier
  modeEvidencePins : ModeEvidencePins

/-- A sealed computation result contains only the mode-native output
representation and its Lean semantic value.  Evidence belongs to the checked
completion token, so an unconstrained duplicate evidence field cannot drift
from the evidence which actually passed the portal. -/
structure CoreResult
    (language : PrivateComputationLanguage) (mode : PrivateComputationKind)
    (PrivateOutput : Type*) where
  outputRepresentation : language.OutputArtifact mode
  privateOutput : PrivateOutput

/-- The exact release-free statement checked by a mode-specific portal.  The
relation and mode pins are part of the statement rather than ambient manifest
metadata.  Resource effects, footprints, and nullifiers remain in the complete
request consumed by the kernel join.  Transition authority remains solely in
the common request-indexed kernel token. -/
structure CoreStatement
    (language : PrivateComputationLanguage) (mode : PrivateComputationKind)
    (Relation SemanticInput OutputCommitment PrivateOutput ModeEvidencePins : Type*) where
  program : language.Program mode
  relation : Relation
  inputValue : SemanticInput
  inputArtifact : language.InputArtifact mode
  outputCommitment : OutputCommitment
  outputArtifact : language.OutputArtifact mode
  privateOutput : PrivateOutput
  modeEvidencePins : ModeEvidencePins

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

/-- The result of private computation before any disclosure decision.  Unlike
`PrivateComputationOutcome`, this type has no release value or declared release
effect.  It is the result type accepted by sealed computation paths. -/
structure PrivateComputationResult
    (language : PrivateComputationLanguage) (mode : PrivateComputationKind)
    (OutputCommitment PrivateOutput : Type*) where
  output : CommittedPrivateOutput OutputCommitment
    (language.OutputArtifact mode) PrivateOutput
  evidence : language.Evidence mode

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

/-! ## Authored release-free computation semantics -/

/-- One authored sealed-computation dialect.  The representation bridge checks
the exact canonical and mode-native input identities; the mode portal checks
the request-derived core statement.  Transition authority is deliberately not
present here: the kernel's common request-indexed `Authorized` token is its sole
owner.  None of these fields can inspect disclosure metadata because no such
metadata occurs in their domain types. -/
structure ComputationDeclaration
    (language : PrivateComputationLanguage) (mode : PrivateComputationKind)
    (Relation BridgeName CanonicalInput SemanticInput
      InputSourceWitness InputTargetWitness OutputCommitment
      PrivateOutput ResourceEffect Footprint Nullifier ModeEvidencePins : Type*) where
  inputBridge : NamedRepresentationBridge BridgeName CanonicalInput InputSourceWitness
    (language.InputArtifact mode) InputTargetWitness SemanticInput
  computationPortal : PrivateEvidencePortal
    (CoreStatement language mode Relation SemanticInput OutputCommitment PrivateOutput
      ModeEvidencePins)
    (language.Evidence mode)

namespace ComputationDeclaration

variable
    {language : PrivateComputationLanguage} {mode : PrivateComputationKind}
    {Relation BridgeName CanonicalInput SemanticInput
      InputSourceWitness InputTargetWitness OutputCommitment
      PrivateOutput ResourceEffect Footprint Nullifier ModeEvidencePins : Type*}
    (declaration : ComputationDeclaration language mode Relation BridgeName
      CanonicalInput SemanticInput InputSourceWitness InputTargetWitness
      OutputCommitment PrivateOutput
      ResourceEffect Footprint Nullifier ModeEvidencePins)

abbrev Request :=
  let _declarationMarker := declaration
  CoreRequest language mode Relation BridgeName CanonicalInput
    SemanticInput OutputCommitment ResourceEffect Footprint Nullifier ModeEvidencePins

abbrev Result :=
  let _declarationMarker := declaration
  CoreResult language mode PrivateOutput

def statementOf (request : declaration.Request) (result : declaration.Result) :
    CoreStatement language mode Relation SemanticInput OutputCommitment PrivateOutput
      ModeEvidencePins where
  program := request.program
  relation := request.relation
  inputValue := request.inputValue
  inputArtifact := request.computationInput
  outputCommitment := request.outputCommitment
  outputArtifact := result.outputRepresentation
  privateOutput := result.privateOutput
  modeEvidencePins := request.modeEvidencePins

/-- The mode/input token for sealed work.  It is not transition authority.
Evidence is indexed by the exact request-derived statement, and the input
bridge is indexed by the exact two representations and semantic input carried
by the request. -/
structure Completion (request : declaration.Request) (result : declaration.Result) where
  inputIdentity : declaration.inputBridge.CheckedIdentity request.inputBridgeName
    request.canonicalInput request.computationInput request.inputValue
  computation : CheckedPrivateEvidence declaration.computationPortal
    (declaration.statementOf request result)

theorem Completion.implies_computation_semantics
    {request : declaration.Request} {result : declaration.Result}
    (completion : declaration.Completion request result) :
    SameOpening declaration.inputBridge.sourceSemantics
        declaration.inputBridge.targetSemantics
        request.canonicalInput completion.inputIdentity.sourceWitness
        request.computationInput completion.inputIdentity.targetWitness ∧
      declaration.computationPortal.Accepts
        (declaration.statementOf request result) completion.computation.witness := by
  exact ⟨completion.inputIdentity.sameOpening, completion.computation.accepts⟩

end ComputationDeclaration

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
  let _declarationMarker := declaration
  PrivateComputationRequest language mode Observer Policy Recipient Purpose BridgeName
    AuthorizationContext CanonicalInput SemanticInput DeclassificationAuthority

abbrev Outcome :=
  let _declarationMarker := declaration
  PrivateComputationOutcome language mode OutputCommitment PrivateOutput
    DeclassificationAuthority Release

/-- The private-computation result prior to a separate disclosure effect. -/
abbrev ComputationOutcome :=
  let _declarationMarker := declaration
  PrivateComputationResult language mode OutputCommitment PrivateOutput

/-- Compatibility data for forgetting a legacy release-capable request into
the release-free core.  Fields which did not exist in the legacy syntax are
authored explicitly here.  The projection below erases all disclosure metadata
and has intentionally no inverse. -/
structure LegacyCoreProjection
    (Relation ResourceEffect Footprint Nullifier ModeEvidencePins : Type*) where
  relation : declaration.Request → Relation
  resourceEffects : declaration.Request → declaration.ComputationOutcome →
    List ResourceEffect
  footprint : declaration.Request → declaration.ComputationOutcome → Footprint
  nullifier : declaration.Request → declaration.ComputationOutcome → Option Nullifier
  modeEvidencePins : declaration.Request → ModeEvidencePins

/-- One-way legacy compatibility: forget policy, observer, recipient, purpose,
reveal/declassification intent, and every release carrier.  There is no
`CoreRequest -> PrivateComputationRequest` construction because supplying the
missing disclosure authorization would be a new semantic act. -/
def LegacyCoreProjection.request
    {Relation ResourceEffect Footprint Nullifier ModeEvidencePins : Type*}
    (projection : declaration.LegacyCoreProjection Relation ResourceEffect Footprint
      Nullifier ModeEvidencePins)
    (request : declaration.Request) (outcome : declaration.ComputationOutcome) :
    CoreRequest language mode Relation BridgeName CanonicalInput
      SemanticInput OutputCommitment ResourceEffect Footprint Nullifier
      ModeEvidencePins where
  program := request.program
  relation := projection.relation request
  canonicalInput := request.canonicalInput
  computationInput := request.computationInput
  inputValue := request.inputValue
  inputBridgeName := request.inputBridgeName
  outputCommitment := outcome.output.commitment
  resourceEffects := projection.resourceEffects request outcome
  footprint := projection.footprint request outcome
  nullifier := projection.nullifier request outcome
  modeEvidencePins := projection.modeEvidencePins request

/-- One-way legacy compatibility for the result erases the duplicate legacy
evidence field as well as every release carrier. -/
def LegacyCoreProjection.result
    {Relation ResourceEffect Footprint Nullifier ModeEvidencePins : Type*}
    (_projection : declaration.LegacyCoreProjection Relation ResourceEffect Footprint
      Nullifier ModeEvidencePins)
    (outcome : declaration.ComputationOutcome) : CoreResult language mode PrivateOutput where
  outputRepresentation := outcome.output.representation
  privateOutput := outcome.output.privateOutput

/-- Forget the release-bearing extension of a legacy outcome. -/
def Outcome.computation (outcome : declaration.Outcome) :
    declaration.ComputationOutcome where
  output := outcome.output
  evidence := outcome.evidence

def computationStatementOf
    (request : declaration.Request) (outcome : declaration.ComputationOutcome) :
    PrivateComputationStatement language mode SemanticInput OutputCommitment PrivateOutput :=
  let _declarationMarker := declaration
  {
    program := request.program
    inputValue := request.inputValue
    inputArtifact := request.computationInput
    outputCommitment := outcome.output.commitment
    outputArtifact := outcome.output.representation
    privateOutput := outcome.output.privateOutput
  }

def statementOf (request : declaration.Request) (outcome : declaration.Outcome) :
    PrivateComputationStatement language mode SemanticInput OutputCommitment PrivateOutput :=
  let _declarationMarker := declaration
  {
    program := request.program
    inputValue := request.inputValue
    inputArtifact := request.computationInput
    outputCommitment := outcome.output.commitment
    outputArtifact := outcome.output.representation
    privateOutput := outcome.output.privateOutput
  }

/-- Completion of the private computation itself.  This token contains the
three authority/meaning legs required to accept private work: request
authorization, exact input representation identity, and mode-specific
computation evidence.  It deliberately contains no release, declassification,
or output-opening authority. -/
structure ComputationCompletion
    (request : declaration.Request) (outcome : declaration.ComputationOutcome) where
  authorization : CheckedPrivateEvidence declaration.authorizationPortal request
  inputIdentity : declaration.inputBridge.CheckedIdentity request.inputBridgeName
    request.canonicalInput request.computationInput request.inputValue
  computation : CheckedPrivateEvidence declaration.computationPortal
    (declaration.computationStatementOf request outcome)

/-- A release-capable completion adds the independent output-opening/policy
judgment and exact declared disclosure to the same computation legs.  Code
which only accepts sealed computation must consume `ComputationCompletion`,
not this stronger type. -/
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

/-- Computation completion exposes exactly its non-disclosure semantics. -/
theorem ComputationCompletion.implies_computation_semantics
    {request : declaration.Request} {outcome : declaration.ComputationOutcome}
    (completion : declaration.ComputationCompletion request outcome) :
    declaration.authorizationPortal.Accepts request completion.authorization.witness ∧
      SameOpening declaration.inputBridge.sourceSemantics
        declaration.inputBridge.targetSemantics
        request.canonicalInput completion.inputIdentity.sourceWitness
        request.computationInput completion.inputIdentity.targetWitness ∧
      declaration.computationPortal.Accepts
        (declaration.computationStatementOf request outcome)
        completion.computation.witness := by
  exact ⟨completion.authorization.accepts,
    completion.inputIdentity.sameOpening,
    completion.computation.accepts⟩

/-- A legacy release-capable completion has a computation-only projection, but
the reverse direction is intentionally unavailable. -/
def Completion.toComputationCompletion [DecidableEq Release]
    {request : declaration.Request} {outcome : declaration.Outcome}
    (completion : declaration.Completion request outcome) :
    declaration.ComputationCompletion request outcome.computation where
  authorization := completion.authorization
  inputIdentity := completion.inputIdentity
  computation := by
    simpa only [computationStatementOf, Outcome.computation, statementOf] using
      completion.computation

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
