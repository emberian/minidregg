/- Joint invocation laws over arbitrary commands and loaded state. The native
multi-principal positive/refusal journey lives in probe-native-host-cli.lean. -/
import Kernel.DeclaredResourceController

namespace Minidregg.Kernel.DeclaredResourceController
open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CellState
open Minidregg.Kernel.MultiCellHyperedge
set_option autoImplicit false

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient}
  {durable : Durable} {command : Command}

theorem empty_targets_refused (subject : SubjectId) (root : Digest) (nonce : Nat) :
    prepare deployment profile ambient durable ⟨subject, root, nonce, []⟩ = .error .emptyTargets := by
  simp [prepare]

theorem duplicate_targets_refused (nonempty : command.targets ≠ [])
    (duplicate : ¬(command.targets.map Target.target).Nodup) :
    prepare deployment profile ambient durable command = .error .duplicateTargets := by
  simp [prepare, nonempty, duplicate]

theorem prepared_targets_valid (prepared : PreparedInvocation deployment profile ambient durable command) :
    command.targetsWellFormed = true :=
  (Command.targetsWellFormed_iff command).mpr ⟨prepared.nonempty, prepared.distinct⟩

/-- A mutation-only participant cannot be exposed to a foreign resource law,
even if every ordinary mutation signature and predicate would otherwise pass. -/
theorem no_joint_acceptance_without_read_capability [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (multiple : 1 < command.targets.length) (i : TargetIndex command)
    (missing : command.targets[i].observeCapability = none) :
    ¬ Nonempty (AcceptedInvocation prepared signed) := by
  rintro ⟨accepted⟩
  have needed : command.requiresObservation = true := by
    simp [Command.requiresObservation, multiple]
  have present := (accepted.observations needed i).capabilityPresent
  simp only [Fin.getElem_fin] at missing
  simp [missing] at present

/-- Native mode evidence states actual source computation, not a Boolean
assertion or an arbitrary proposed post beside the authored command. -/
theorem prepared_computation_exact (prepared : PreparedInvocation deployment profile ambient durable command)
    (i : TargetIndex command) :
    computeTarget deployment prepared.authority.snapshot profile.semantics ambient command
      command.targets[i] (prepared.targets i).pre = .ok (prepared.targets i).post :=
  (prepared.targets i).candidate.modeEvidence.down

/-- Refusing even one authored target prevents a complete transaction from
existing. Successful earlier computations do not become accepted sub-turns. -/
theorem failed_target_cannot_prepare (prepared : PreparedInvocation deployment profile ambient durable command)
    (i : TargetIndex command) (reason : Reject)
    (failed : computeTarget deployment prepared.authority.snapshot profile.semantics ambient command
      command.targets[i] (prepared.targets i).pre = .error reason) : False := by
  rw [prepared_computation_exact prepared i] at failed
  cases failed

/-- Both local and neighboring policy observations equal the exact final
states eventually carried by the accepted multi-cell declaration. -/
theorem accepted_joint_projection_exact [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) (i : TargetIndex command) :
    project prepared (some i) accepted.tuple.source
      (fun incidence => (accepted.declaration.post accepted.legs incidence).logical) =
    project prepared (some i) accepted.tuple.source accepted.tuple.logicalPost :=
  accepted.policy_view_exact (some i)

def acceptedTargetPost [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) (i : TargetIndex command) :
    TargetCell command.targets[i] := by
  change Materialized ((layout prepared).materializer (some i))
  exact accepted.declaration.post accepted.legs (some i)

/-- The physical registry law holds on the actual accepted target post,
not merely a different local candidate that happened to pass earlier. -/
theorem accepted_target_final_law [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) (i : TargetIndex command) :
    CanonicalCellRegistry.FinalPostLaw deployment command.targets[i].target (prepared.targets i).before
      (packTarget command.targets[i] (acceptedTargetPost accepted i)) := by
  letI : DecidableEq ((layout prepared).schema (some i)).Field :=
    (layout prepared).fieldDecidableEq (some i)
  letI : DecidableEq ((layout prepared).schema (some i)).Resource :=
    (layout prepared).resourceDecidableEq (some i)
  have exactPost : acceptedTargetPost accepted i = (prepared.targets i).candidate.post := by
    change accepted.declaration.post accepted.legs (some i) = (validated prepared (some i)).apply
    exact accepted.post_exact (some i)
  rw [exactPost]
  exact (prepared.targets i).postLaw

/-- One subject/nonce cannot evade prior operation identity by replacing the
payload, target list or expected state. The exact ingress lookup distinguishes
an identical retry from a conflicting use of that identity. -/
theorem changed_body_keeps_operation_identity (domain semantics : Digest)
    (left right : Command) (subject : left.subject = right.subject) (nonce : left.nonce = right.nonce) :
    operationMarker domain semantics left = operationMarker domain semantics right := by
  simp only [operationMarker, subject, nonce]

/-- Canonical source bytes distinguish every unequal source command before
hashing; no unproved collision-resistance claim is smuggled into this law. -/
theorem unequal_commands_have_unequal_bytes (left right : Command) (different : left ≠ right) :
    commandCodec.encode left ≠ commandCodec.encode right := by
  intro same
  have decoded := congrArg commandCodec.decode same
  rw [commandCodec.decode_encode, commandCodec.decode_encode] at decoded
  exact different (Option.some.inj decoded)

/-- Every finite transaction publishes one replay nullifier, independent of
the number of participants or physical authority pages touched. -/
theorem accepted_exactly_one_nullifier [DecidableEq F]
    {prepared : PreparedInvocation deployment profile ambient durable command} {signed : SignedCommand}
    (accepted : AcceptedInvocation prepared signed) (shape : PhysicalShape prepared) :
    (accepted.dataIntent shape).nullifiers =
      [invocationNullifier prepared.authority.snapshot.domain
        (operationMarker prepared.authority.snapshot.domain profile.semantics command)] := rfl

/-- info: 'Minidregg.Kernel.DeclaredResourceController.empty_targets_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms empty_targets_refused
/-- info: 'Minidregg.Kernel.DeclaredResourceController.duplicate_targets_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms duplicate_targets_refused
/-- info: 'Minidregg.Kernel.DeclaredResourceController.prepared_targets_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prepared_targets_valid
/-- info: 'Minidregg.Kernel.DeclaredResourceController.no_joint_acceptance_without_read_capability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_joint_acceptance_without_read_capability
/-- info: 'Minidregg.Kernel.DeclaredResourceController.prepared_computation_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prepared_computation_exact
/-- info: 'Minidregg.Kernel.DeclaredResourceController.failed_target_cannot_prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms failed_target_cannot_prepare
/-- info: 'Minidregg.Kernel.DeclaredResourceController.accepted_joint_projection_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted_joint_projection_exact
/-- info: 'Minidregg.Kernel.DeclaredResourceController.accepted_target_final_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted_target_final_law
/-- info: 'Minidregg.Kernel.DeclaredResourceController.changed_body_keeps_operation_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms changed_body_keeps_operation_identity
/-- info: 'Minidregg.Kernel.DeclaredResourceController.unequal_commands_have_unequal_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unequal_commands_have_unequal_bytes
/-- info: 'Minidregg.Kernel.DeclaredResourceController.accepted_exactly_one_nullifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted_exactly_one_nullifier
end Minidregg.Kernel.DeclaredResourceController
