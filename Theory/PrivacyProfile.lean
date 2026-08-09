/-
# Theory.PrivacyProfile — candidate-independent privacy semantics

Privacy is recorded as four independent observations.  In particular, a
cryptographic hiding statement is only a statement carried by a profile; this
file neither realizes nor assumes one for any concrete primitive.
-/
import Mathlib.Tactic

namespace Minidregg.Theory

/-- The privacy profile of a dialect state or a portal artifact.  The four
fields are deliberately independent: no field is a theorem about another. -/
structure PrivacyProfile
    (State Observer Principal PublicObservation ExecutionObservation MetadataObservation :
      Type*) where
  /-- The value intentionally exposed to a particular observer. -/
  publicView : Observer → State → PublicObservation
  /-- The cryptographic hiding statement a concrete realization would have to
  discharge.  Merely populating this predicate proves no cryptography. -/
  cryptographicHidingClaim : Observer → State → State → Prop
  /-- What a principal participating in execution can observe. -/
  executionVisibility : Principal → State → ExecutionObservation
  /-- Transcript and access-pattern metadata visible to an observer. -/
  metadataView : Observer → State → MetadataObservation

def PrivacyProfile.PublicEquivalent
    {State Observer Principal PublicObservation ExecutionObservation MetadataObservation :
      Type*}
    (profile : PrivacyProfile State Observer Principal PublicObservation
      ExecutionObservation MetadataObservation)
    (observer : Observer) (left right : State) : Prop :=
  profile.publicView observer left = profile.publicView observer right

def PrivacyProfile.ExecutionEquivalent
    {State Observer Principal PublicObservation ExecutionObservation MetadataObservation :
      Type*}
    (profile : PrivacyProfile State Observer Principal PublicObservation
      ExecutionObservation MetadataObservation)
    (principal : Principal) (left right : State) : Prop :=
  profile.executionVisibility principal left = profile.executionVisibility principal right

def PrivacyProfile.MetadataEquivalent
    {State Observer Principal PublicObservation ExecutionObservation MetadataObservation :
      Type*}
    (profile : PrivacyProfile State Observer Principal PublicObservation
      ExecutionObservation MetadataObservation)
    (observer : Observer) (left right : State) : Prop :=
  profile.metadataView observer left = profile.metadataView observer right

/-- The complete observer-side equivalence used by noninterference.  Public
payload equality alone is insufficient when metadata differs. -/
def PrivacyProfile.ObserverEquivalent
    {State Observer Principal PublicObservation ExecutionObservation MetadataObservation :
      Type*}
    (profile : PrivacyProfile State Observer Principal PublicObservation
      ExecutionObservation MetadataObservation)
    (observer : Observer) (left right : State) : Prop :=
  profile.PublicEquivalent observer left right ∧
    profile.MetadataEquivalent observer left right

/-- A typed map between dialects (or between a dialect and a portal boundary),
including the corresponding observer translation. -/
structure PrivacyPortal (Source Target SourceObserver TargetObserver : Type*) where
  run : Source → Target
  mapObserver : SourceObserver → TargetObserver

def PrivacyPortal.comp
    {A B C OA OB OC : Type*}
    (second : PrivacyPortal B C OB OC) (first : PrivacyPortal A B OA OB) :
    PrivacyPortal A C OA OC where
  run := second.run ∘ first.run
  mapObserver := second.mapObserver ∘ first.mapObserver

/-- A portal preserves observer noninterference when indistinguishable source
states remain indistinguishable at its target boundary. -/
def PrivacyPortal.PreservesObservation
    {Source Target SourceObserver TargetObserver SourcePrincipal TargetPrincipal
      SourcePublic SourceExecution SourceMetadata TargetPublic TargetExecution TargetMetadata :
      Type*}
    (portal : PrivacyPortal Source Target SourceObserver TargetObserver)
    (sourceProfile : PrivacyProfile Source SourceObserver SourcePrincipal SourcePublic
      SourceExecution SourceMetadata)
    (targetProfile : PrivacyProfile Target TargetObserver TargetPrincipal TargetPublic
      TargetExecution TargetMetadata) : Prop :=
  ∀ observer left right,
    sourceProfile.ObserverEquivalent observer left right →
      targetProfile.ObserverEquivalent (portal.mapObserver observer)
        (portal.run left) (portal.run right)

/-- Basic composition theorem: two explicitly observation-preserving portals
compose to an observation-preserving portal.  No cryptographic or execution-
privacy premise is smuggled into observer equivalence. -/
theorem PrivacyPortal.compose_noninterference
    {A B C OA OB OC PA PB PC PubA ExecA MetaA PubB ExecB MetaB PubC ExecC MetaC : Type*}
    (first : PrivacyPortal A B OA OB) (second : PrivacyPortal B C OB OC)
    (profileA : PrivacyProfile A OA PA PubA ExecA MetaA)
    (profileB : PrivacyProfile B OB PB PubB ExecB MetaB)
    (profileC : PrivacyProfile C OC PC PubC ExecC MetaC)
    (hfirst : first.PreservesObservation profileA profileB)
    (hsecond : second.PreservesObservation profileB profileC) :
    (second.comp first).PreservesObservation profileA profileC := by
  intro observer left right hview
  exact hsecond (first.mapObserver observer) (first.run left) (first.run right)
    (hfirst observer left right hview)

/-! ## Typed private joins -/

/-- The opening relation for one representation of a semantic value. -/
structure OpeningSemantics (Artifact Witness Value : Type*) where
  opens : Artifact → Witness → Value → Prop

/-- Two differently typed artifacts have the same opening exactly when their
respective witnesses open them to one common semantic value. -/
def SameOpening
    {SourceArtifact SourceWitness TargetArtifact TargetWitness Value : Type*}
    (source : OpeningSemantics SourceArtifact SourceWitness Value)
    (target : OpeningSemantics TargetArtifact TargetWitness Value)
    (sourceArtifact : SourceArtifact) (sourceWitness : SourceWitness)
    (targetArtifact : TargetArtifact) (targetWitness : TargetWitness) : Prop :=
  ∃ value,
    source.opens sourceArtifact sourceWitness value ∧
      target.opens targetArtifact targetWitness value

/-- The semantics of an authorized private-output projection. -/
structure ReleaseSemantics (Policy Recipient Purpose PrivateOutput Release : Type*) where
  permitted : Policy → Recipient → Purpose → PrivateOutput → Prop
  project : Policy → Recipient → Purpose → PrivateOutput → Release

/-- A release is authorized only when policy permits the private output and the
released value is exactly the policy-selected projection. -/
def AuthorizedRelease
    {Policy Recipient Purpose PrivateOutput Release : Type*}
    (semantics : ReleaseSemantics Policy Recipient Purpose PrivateOutput Release)
    (policy : Policy) (recipient : Recipient) (purpose : Purpose)
    (privateOutput : PrivateOutput) (release : Release) : Prop :=
  semantics.permitted policy recipient purpose privateOutput ∧
    release = semantics.project policy recipient purpose privateOutput

/-- Private differences outside an equal authorized projection do not affect
the released value.  Permission and projection equality are explicit premises. -/
theorem authorizedRelease_noninterference
    {Policy Recipient Purpose PrivateOutput Release : Type*}
    (semantics : ReleaseSemantics Policy Recipient Purpose PrivateOutput Release)
    (policy : Policy) (recipient : Recipient) (purpose : Purpose)
    (left right : PrivateOutput) (leftRelease rightRelease : Release)
    (hleft : AuthorizedRelease semantics policy recipient purpose left leftRelease)
    (hright : AuthorizedRelease semantics policy recipient purpose right rightRelease)
    (hprojection : semantics.project policy recipient purpose left =
      semantics.project policy recipient purpose right) :
    leftRelease = rightRelease :=
  hleft.2.trans (hprojection.trans hright.2.symm)

/-! ## Independence refuters -/

private def executorLeakProfile : PrivacyProfile Bool Unit Unit Unit Bool Unit where
  publicView := fun _ _ => ()
  cryptographicHidingClaim := fun _ _ _ => True
  executionVisibility := fun _ secret => secret
  metadataView := fun _ _ => ()

/-- A commitment-hiding claim and equal public/metadata views do not imply that
an executor cannot distinguish the secrets. -/
theorem commitmentHidingClaim_does_not_imply_executorPrivacy :
    executorLeakProfile.cryptographicHidingClaim () false true ∧
      executorLeakProfile.PublicEquivalent () false true ∧
      executorLeakProfile.MetadataEquivalent () false true ∧
      ¬executorLeakProfile.ExecutionEquivalent () false true := by
  simp [executorLeakProfile, PrivacyProfile.PublicEquivalent,
    PrivacyProfile.MetadataEquivalent, PrivacyProfile.ExecutionEquivalent]

private def metadataLeakProfile : PrivacyProfile Bool Unit Unit Unit Unit Bool where
  publicView := fun _ _ => ()
  cryptographicHidingClaim := fun _ _ _ => True
  executionVisibility := fun _ _ => ()
  metadataView := fun _ secret => secret

/-- An encryption-hiding claim and even equal execution views do not imply
metadata or access-pattern privacy. -/
theorem encryptionHidingClaim_does_not_imply_metadataPrivacy :
    metadataLeakProfile.cryptographicHidingClaim () false true ∧
      metadataLeakProfile.PublicEquivalent () false true ∧
      metadataLeakProfile.ExecutionEquivalent () false true ∧
      ¬metadataLeakProfile.MetadataEquivalent () false true := by
  simp [metadataLeakProfile, PrivacyProfile.PublicEquivalent,
    PrivacyProfile.ExecutionEquivalent, PrivacyProfile.MetadataEquivalent]

end Minidregg.Theory
