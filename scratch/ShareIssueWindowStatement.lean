/-
STATEMENT ONLY, no proofs: every Prop below is stated and unproven (no `sorry` is used; they are `def ... : Prop`). For the auditor (af7a93e7b8ba729d4) before any proof work.

Problem. A grain-backed share issue is planned at height p: the ticket's root grants carry
`notBefore := p` and `notAfter := p + record.lifetime`
(Kernel/ApplicationShareIssueSource.lean:213-214, in `rootCapability`, reached through
`Ready.descriptor`), signed into `decoded.source.birth`. Admission rebuilds the descriptor at the
SUBMIT height h = `ambient.height = NativeHost.logicalHeight config durable = genesisHeight +
accepted-turn count` and requires equality
(Kernel/ApplicationShareIssueGrainAdmission.lean, `Accepted.sourceDescriptor` at lines 63-68 and
the byte-equality test in `admitNative`). So one accepted turn between plan and submit changes h,
the rebuilt descriptor differs from the signed one, and the issue is refused. The clock is the
accepted-turn count, so a busy room hits this.

Statement. Admission derives the window from the plan's signed height p, not from h: it accepts
exactly when some p with p <= h < p + lifetime makes the signed descriptor equal the descriptor
rebuilt at p. The rest of the descriptor is unchanged (issuer, payer, funding, tariff, nonce,
births, policies).
-/
import Kernel.ApplicationShareIssueGrainAdmission

namespace Minidregg.Kernel.ApplicationShareIssueGrainAdmission
open Minidregg.Compiler Minidregg.Theory Minidregg.Theory.ResourceBirth Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CellRegistry Minidregg.Theory.CellState Minidregg.Kernel.ApplicationShareIssueSource

variable {F : Type} [Field F] [DecidableEq F]

/-- The descriptor of the ticket rebuilt as if planned at height `p`. This is the existing
`Ready.expectedDescriptor` with `p` in place of `ambient.height`; nothing else varies. -/
def descriptorPlannedAt {profile : CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config}
    {spec : Spec}
    (ready : Ready config.deployment.domain spec
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.issuer spec.ticket.issueNonce).value)
    (record : PlatformCellLayout.Platform) (authority : AuthState) (p : Nat)
    (payer : Nat) (funding : List InitialFunding) (auxiliaryCreates : List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry)) :
    Descriptor CanonicalCellRegistry.registry :=
  { ready.expectedDescriptor profile config record authority p payer funding with
    auxiliaryCreates := auxiliaryCreates }

/-- The relaxed acceptance: the signed ticket descriptor is the one planned at some height `p`
that is not in the future of the submit height `h` and whose window has not closed. -/
def PlannedWithinWindow {profile : CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config}
    {spec : Spec}
    (ready : Ready config.deployment.domain spec
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.issuer spec.ticket.issueNonce).value)
    (record : PlatformCellLayout.Platform) (authority : AuthState) (h : Nat)
    (signed : Descriptor CanonicalCellRegistry.registry) (auxiliaryCreates : List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry)) : Prop :=
  ∃ p, p ≤ h ∧ h < p + record.lifetime ∧
    signed = descriptorPlannedAt ready record authority p signed.fee.payer signed.funding auxiliaryCreates

/-- Pole 1, satisfiable: planned at p, one accepted tick, submitted at p + 1 is accepted
(so long as the window is more than one tick wide). -/
def pole_admits_after_one_tick : Prop :=
  ∀ {profile : CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config} {spec : Spec}
    (ready : Ready config.deployment.domain spec
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.issuer spec.ticket.issueNonce).value)
    (record : PlatformCellLayout.Platform) (authority : AuthState) (p : Nat)
    (payer : Nat) (funding : List InitialFunding) (aux : List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry)),
    1 < record.lifetime →
    PlannedWithinWindow ready record authority (p + 1)
      (descriptorPlannedAt ready record authority p payer funding aux) aux

/-- Pole 2a, teeth (expiry): at or after `notAfter = p + lifetime` the issue is refused. -/
def pole_refuses_expired : Prop :=
  ∀ {profile : CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config} {spec : Spec}
    (ready : Ready config.deployment.domain spec
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.issuer spec.ticket.issueNonce).value)
    (record : PlatformCellLayout.Platform) (authority : AuthState) (p h : Nat)
    (payer : Nat) (funding : List InitialFunding) (aux : List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry)),
    p + record.lifetime ≤ h →
    ¬ PlannedWithinWindow ready record authority h
        (descriptorPlannedAt ready record authority p payer funding aux) aux

/-- Pole 2b, teeth (any other byte): a descriptor that differs from every height-planned rebuild,
for instance a different payer-independent field such as the issuer's policy list, is refused. -/
def pole_refuses_altered : Prop :=
  ∀ {profile : CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config} {spec : Spec}
    (ready : Ready config.deployment.domain spec
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.issuer spec.ticket.issueNonce).value)
    (record : PlatformCellLayout.Platform) (authority : AuthState) (h : Nat)
    (signed : Descriptor CanonicalCellRegistry.registry) (aux : List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry)),
    (∀ p, signed ≠ descriptorPlannedAt ready record authority p signed.fee.payer signed.funding aux) →
    ¬ PlannedWithinWindow ready record authority h signed aux

/-- Pole 2c, teeth (future plan): a descriptor planned at a height above the submit height is
refused (p <= h). -/
def pole_refuses_future_plan : Prop :=
  ∀ {profile : CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config} {spec : Spec}
    (ready : Ready config.deployment.domain spec
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.issuer spec.ticket.issueNonce).value)
    (record : PlatformCellLayout.Platform) (authority : AuthState) (p h : Nat)
    (payer : Nat) (funding : List InitialFunding) (aux : List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry)),
    h < p →
    (∀ q, q ≤ h → descriptorPlannedAt ready record authority q payer funding aux ≠
      descriptorPlannedAt ready record authority p payer funding aux) →
    ¬ PlannedWithinWindow ready record authority h
        (descriptorPlannedAt ready record authority p payer funding aux) aux

/-- Premise inhabitation: a record with `lifetime > 1`, and a ready ticket over it, exist for the
production profile (the platform record's `lifetime` pin is positive; the existing grain-issue
fixtures instantiate `Ready`). To be discharged against `Fixtures.NativeAcceptedFixture`. -/
def premise_inhabited : Prop :=
  ∃ (profile : CanonicalRuntimeProfile.Profile F) (config : NativeHost.Config) (spec : Spec)
    (_ready : Ready config.deployment.domain spec
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.issuer spec.ticket.issueNonce).value)
    (record : PlatformCellLayout.Platform), 1 < record.lifetime

/-- Determinacy of the plan height. The grants of `descriptorPlannedAt` carry `notBefore := p` in
their root capabilities (`rootCapability`, ApplicationShareIssueSource.lean:215), so two plan heights
that rebuild the same descriptor are equal: the `∃ p` in `PlannedWithinWindow` is one p. -/
def lemma_plan_height_determined : Prop :=
  ∀ {profile : CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config} {spec : Spec}
    (ready : Ready config.deployment.domain spec
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.issuer spec.ticket.issueNonce).value)
    (record : PlatformCellLayout.Platform) (authority : AuthState) (p q : Nat)
    (payer : Nat) (funding : List InitialFunding) (aux : List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry)),
    descriptorPlannedAt ready record authority p payer funding aux =
      descriptorPlannedAt ready record authority q payer funding aux → p = q

/- App-delegation leg. `ApplicationShareIssueDelegation.prepare` is called at `ambient.height`
(admitNative, line 141) and `appRequest` puts that `height` into the signed request, so the
signature in `ingress.appEnvelope` (made at the PLAN height) has the same submit-height mismatch.
The leg is therefore windowed by the same `p`. Its policy epoch and revision come from the loaded
authority and stay checked at submit. NOT covered here, flagged for the auditor:
`GrainResourceBirthController.prepareSourceBirth ... ambient.height` (admitNative, line 117) also
reads the submit height; whether that height reaches the descriptor bytes is not established by
this statement. -/

/-- The relaxed `Accepted.sourceDescriptor` field: it replaces the strict field (descriptor rebuilt
at `ambient.height`) and the strict `appPrepared`/`appChecked` fields (request built at
`ambient.height`) by one conjunction over a single plan height `p`, existential, no wire change.
`Accepted` itself would carry `p` and the three conjuncts as fields; this Prop is that field set.
The grain-side `birth` and the `Checked` read guards stay as they are in `Accepted`. -/
def AcceptedWindowFields {profile : CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config}
    {spec : Spec}
    (ready : Ready config.deployment.domain spec
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.issuer spec.ticket.issueNonce).value)
    (record : PlatformCellLayout.Platform) (authority : AuthState)
    (context : ApplicationShareIssueDelegation.Context config.deployment)
    (h : Nat) (signed : Descriptor CanonicalCellRegistry.registry) (aux : List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry))
    (envelope : List UInt8) : Prop :=
  ∃ p, p ≤ h ∧ h < p + record.lifetime ∧
    signed = descriptorPlannedAt ready record authority p signed.fee.payer signed.funding aux ∧
    ∃ prepared : ApplicationShareIssueDelegation.Prepared context profile config.federation p spec signed,
      Nonempty (ApplicationShareIssueDelegation.Checked prepared envelope)

/-- The descriptor leg of `AcceptedWindowFields` is exactly `PlannedWithinWindow`. -/
def AcceptedWindowFields.descriptor_leg : Prop :=
  ∀ {profile : CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config} {spec : Spec}
    (ready : Ready config.deployment.domain spec
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.issuer spec.ticket.issueNonce).value)
    (record : PlatformCellLayout.Platform) (authority : AuthState)
    (context : ApplicationShareIssueDelegation.Context config.deployment)
    (h : Nat) (signed : Descriptor CanonicalCellRegistry.registry) (aux : List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry)) (envelope : List UInt8),
    AcceptedWindowFields (profile := profile) ready record authority context h signed aux envelope →
      PlannedWithinWindow ready record authority h signed aux

/-- Backward compatibility: the strict (submit-height) acceptance is the window with `p = h`, so
every issue the old `Accepted` admitted is still admitted. -/
def strict_implies_window : Prop :=
  ∀ {profile : CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config} {spec : Spec}
    (ready : Ready config.deployment.domain spec
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.issuer spec.ticket.issueNonce).value)
    (record : PlatformCellLayout.Platform) (authority : AuthState)
    (h : Nat) (signed : Descriptor CanonicalCellRegistry.registry) (aux : List (CreateRequest (CellId := Nat) CanonicalCellRegistry.registry)),
    1 ≤ record.lifetime →
    signed = descriptorPlannedAt ready record authority h signed.fee.payer signed.funding aux →
    PlannedWithinWindow ready record authority h signed aux

end Minidregg.Kernel.ApplicationShareIssueGrainAdmission
