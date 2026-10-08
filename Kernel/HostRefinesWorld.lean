/- Native admission instances of the shared World refinement core. -/
import Kernel.HostRefinesWorldCore
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.HostRefinesWorld

open Minidregg.Theory.Store
open Minidregg.Kernel.World
open Minidregg.Kernel.TurnOfIntent
open Minidregg.Kernel.TurnRecord (ImplementationRefinement Trace trace_represents_fold)
open Minidregg.Theory.ResourceCost (Lane Charge)
open Minidregg.Kernel.DurableCommitProtocol (Snapshot Schedule CrashPoint)
open Minidregg.Kernel.DurableDataIntent
  (DataIntent DataSnapshot StableEvent StableNullifier TransactionId Outcome execute)
open Minidregg.Compiler.DurableReceiverIO (Loaded)
open Minidregg.Kernel.DurableCheckpoint (Ready)
open Minidregg.Kernel.DeployedBridge (deployedR sourceCell)

set_option autoImplicit false

section Represent
variable {R : Registry} {D : Type} [DecidableEq D]

/-- **The clock offset (G-CLOCK, narrowed).**  Under `Represents`, the
deployed logical height every receiver pins (`NativeHost.logicalHeight`) is the
genesis height plus the world's head height: the offset is one constant. -/
theorem represents_logicalHeight (B : Bridge R D)
    {p : Loaded Minidregg.Compiler.ResourceBirthCodec.rootBytes} {w : World R TransactionId D}
    (rep : Represents B p w) (config : NativeHost.Config) :
    ∃ h r, w.head = some (h, r) ∧ NativeHost.logicalHeight config p = config.genesisHeight + h := by
  obtain ⟨r, hr⟩ := rep.head
  exact ⟨p.height, r, hr, rfl⟩

end Represent

/-! ## 4. All 37 constructors: the admitted object is the intent -/

section Admission

variable {R : Registry} {D : Type} [DecidableEq D]

/-- **`Turn.ofIntent` on the admitted object.**  `NativeAdmission config opened`
is indexed by the `DataIntent` it admits: each of its 37 constructors carries
the private receiving object (`AcceptedBirth`, `AcceptedInvocation`, …) whose
intent is that index.  So the turn of an admission is the turn of its index,
and one derivation covers all 37 -- there is no per-constructor `ofIntent`. -/
def Turn.ofAdmission (B : Bridge R D) (H : History R TransactionId StableEvent D)
    (w : World R TransactionId D) {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {intent : DataIntent Minidregg.Compiler.ResourceBirthCodec.rootBytes}
    (_admitted : NativeHostReplay.NativeAdmission config opened intent) :
    Except Refusal (DTurn R D) :=
  Turn.ofIntent B H w intent

/-- The admission form of `ofIntent_run`: an admitted intent the executor
installs, from a represented snapshot, steps the world to a representation of
the installed snapshot. -/
theorem ofAdmission_run (B : Bridge R D) (H : History R TransactionId StableEvent D)
    {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {intent : DataIntent Minidregg.Compiler.ResourceBirthCodec.rootBytes}
    (admitted : NativeHostReplay.NativeAdmission config opened intent)
    {snap : DataSnapshot Minidregg.Compiler.ResourceBirthCodec.rootBytes} {height : Nat}
    {w : World R TransactionId D} (rep : SnapRepresents B snap height w) {t : DTurn R D}
    (derived : Turn.ofAdmission B H w admitted = .ok t)
    (installs : Installs (execute .complete snap intent) = true) :
    ∃ w', World.step H w t = some w' ∧
      SnapRepresents B (DataSnapshot.install snap intent) (height + 1) w' := by
  rcases execute_cases .complete snap intent with ⟨-, fresh, ready, -⟩ | ⟨hi, -⟩
  · exact ofIntent_run B H rep derived fresh ready
  · rw [installs] at hi; cases hi

end Admission

/-! ### The three inferred rows, traced (T3 §2: 13, 14, 16)

Each of `applicationShareIssue`, `applicationGrainShareIssue`,
`applicationAgentLifetimeGrantIssue` admits a nested birth whose descriptor is
pinned to the source's `expectedDescriptor` (`sourceDescriptor`), and that
descriptor carries exactly one initial policy: the ticket / grant policy
record.  So every accepted intent of the three creates one policy-source cell
(through `PreparedBirth.initial_source_write`) -- a ROM birth, a turn since
T3b. -/

theorem shareIssue_birth_has_one_initial_policy {F : Type} [Field F] [DecidableEq F]
    {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config}
    {pins : Minidregg.Theory.ResourceBirth.FactoryPins}
    {durable : ResourceBirthController.Concrete.Durable}
    {height : Minidregg.Theory.TypedAuthorization.Height}
    {ingress : ApplicationShareIssueSource.Ingress}
    (accepted : ApplicationShareIssueAdmission.Accepted profile config pins durable height ingress) :
    accepted.birth.descriptor.initialPolicies.length = 1 := by
  rw [accepted.sourceDescriptor]
  rfl

theorem grainShareIssue_birth_has_one_initial_policy {F : Type} [Field F] [DecidableEq F]
    {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config}
    {pins : Minidregg.Theory.ResourceBirth.FactoryPins}
    {durable : ResourceBirthController.Concrete.Durable}
    {ambient : DeclaredResourceController.Ambient}
    {ingress : ApplicationShareIssueGrainSource.Ingress}
    (accepted : ApplicationShareIssueGrainAdmission.Accepted profile config pins durable ambient
      ingress) :
    accepted.decoded.source.birth.initialPolicies.length = 1 := by
  rw [accepted.sourceDescriptor]
  rfl

theorem lifetimeGrantIssue_birth_has_one_initial_policy {F : Type} [Field F] [DecidableEq F]
    {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} {config : NativeHost.Config}
    {pins : Minidregg.Theory.ResourceBirth.FactoryPins}
    {durable : ResourceBirthController.Concrete.Durable}
    {height : Minidregg.Theory.TypedAuthorization.Height}
    {ingress : ApplicationAgentLifetimeGrantSource.Ingress}
    (accepted : ApplicationAgentLifetimeGrantAdmission.Accepted profile config pins durable height
      ingress) :
    accepted.birth.descriptor.initialPolicies.length = 1 := by
  rw [accepted.sourceDescriptor]
  rfl

#assert_axioms represents_logicalHeight
#assert_axioms ofAdmission_run
#assert_axioms shareIssue_birth_has_one_initial_policy
#assert_axioms grainShareIssue_birth_has_one_initial_policy
#assert_axioms lifetimeGrantIssue_birth_has_one_initial_policy
/-- info: 'Minidregg.Kernel.HostRefinesWorld.ofAdmission_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ofAdmission_run

end Minidregg.Kernel.HostRefinesWorld
