/-
# Revocation teeth: distinct authority, exact command binding, downstream denial

The native acceptance journey is scripts/probe-native-host-cli.lean. These are
kernel-checked codec/scope cases and source-derived general laws, not deployment
claims or substitutes for that signed durable test.
-/
import Kernel.CapabilityRevocationReceiver

namespace Minidregg.Assurance.CapabilityRevocationAudit

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.CapabilityRevocationController

set_option autoImplicit false

def command : Command .object :=
  { subject := ⟨7⟩
    nonce := 4
    target := ⟨55⟩
    victimKind := .object
    capability := ⟨60⟩
    controlCapability := ⟨62⟩
    expectedTargetRoot := ⟨100⟩
    expectedAuthorityRoot := ⟨200⟩ }

theorem canonical_command_roundtrip :
    commandCodec.decode (commandCodec.encode ⟨.object, command⟩) = some ⟨.object, command⟩ :=
  commandCodec.decode_encode _

theorem control_substitution_changes_signed_command :
    commandCodec.encode ⟨.object, { command with controlCapability := ⟨63⟩ }⟩ ≠
      commandCodec.encode ⟨.object, command⟩ := by
  intro same
  have bound := ResourceBirthCodec.lawful_encode_injective commandCodec same
  cases bound

theorem victim_substitution_changes_signed_command :
    commandCodec.encode ⟨.object, { command with capability := ⟨61⟩ }⟩ ≠
      commandCodec.encode ⟨.object, command⟩ := by
  intro same
  have bound := ResourceBirthCodec.lawful_encode_injective commandCodec same
  cases bound

theorem resource_kind_substitution_changes_signed_command :
    commandCodec.encode ⟨.program,
      { subject := command.subject, nonce := command.nonce, target := ⟨55⟩,
        victimKind := command.victimKind, capability := command.capability,
        controlCapability := command.controlCapability, expectedTargetRoot := command.expectedTargetRoot,
        expectedAuthorityRoot := command.expectedAuthorityRoot }⟩ ≠
      commandCodec.encode ⟨.object, command⟩ := by
  intro same
  have bound := ResourceBirthCodec.lawful_encode_injective commandCodec same
  cases bound

theorem victim_kind_substitution_changes_signed_command :
    commandCodec.encode ⟨.object, { command with victimKind := .program }⟩ ≠
      commandCodec.encode ⟨.object, command⟩ := by
  intro same
  have bound := ResourceBirthCodec.lawful_encode_injective commandCodec same
  cases bound

theorem authority_root_substitution_changes_signed_command :
    commandCodec.encode ⟨.object, { command with expectedAuthorityRoot := ⟨201⟩ }⟩ ≠
      commandCodec.encode ⟨.object, command⟩ := by
  intro same
  have bound := ResourceBirthCodec.lawful_encode_injective commandCodec same
  cases bound

theorem authority_verbs_distinct :
    CredentialAuthorityEntryCodec.verbTag (.revokeCapability) ≠
      CredentialAuthorityEntryCodec.verbTag (.installPolicy) := by decide

theorem receipt_verbs_distinct :
    Minidregg.Theory.AuthorizationDeclaration.verbTag (.revokeCapability) ≠
      Minidregg.Theory.AuthorizationDeclaration.verbTag (.installPolicy) := by decide

/-- Revoking a parent refutes ordinary use AND later delegation: the argument
is any request, so the verb cannot route around the ancestor check. -/
theorem revoked_parent_denies_every_verb {kind : ResourceKind}
    (capability : Capability kind) (state : AuthState) (parent : CapabilityId)
    (ancestor : parent ∈ capability.ancestors)
    (revoked : RevocationKey.capability parent ∈ state.revoked) :
    ∀ request : Request kind, ¬ capability.Admissible state request :=
  fun request => ancestor_revocation_rejected capability state request parent ancestor revoked

/-- Closed hostile case over the pre-existing inhabited authority fixture. -/
theorem inherited_revocation_denies_demo :
    ¬ demoCapability.Admissible { demoState with revoked := {.capability demoCapability.id} } demoRequest := by
  intro admitted
  exact admitted.selfNotRevoked (by simp)

def emptyAuthority : ResourceAuthorityProjection.Authority where
  fields := 0
  resources := fun resource => nomatch resource

/-- An actual unrelated subject-key epoch change is invisible, even though
full-domain serialization would have changed and leaked it to the policy. -/
theorem foreign_key_epoch_invisible :
    ResourceAuthorityProjection.grantSlots "authority/victim" .object ⟨60⟩
      { emptyAuthority with fields := emptyAuthority.fields.write (.subjectKeyEpoch ⟨900⟩) (37 : Nat) } =
    ResourceAuthorityProjection.grantSlots "authority/victim" .object ⟨60⟩ emptyAuthority :=
  ResourceAuthorityProjection.grantSlots_write_unselected _ _ _ _ _ _ (by decide) (by decide)

/-- The relevant revocation IS visible: the noninterference law has teeth and
has not erased the operation's before/after distinction. -/
theorem selected_revocation_visible :
    ResourceAuthorityProjection.grantSlots "authority/victim" .object ⟨60⟩
      { emptyAuthority with fields := emptyAuthority.fields.write (.revoked (.capability ⟨60⟩)) true } ≠
    ResourceAuthorityProjection.grantSlots "authority/victim" .object ⟨60⟩ emptyAuthority := by
  intro same
  have prefixExact := congrArg (List.take 2) same
  rw [ResourceAuthorityProjection.grantSlots_status, ResourceAuthorityProjection.grantSlots_status] at prefixExact
  simp [ResourceAuthorityProjection.selfRevoked, emptyAuthority, CellState.FieldStore.write, CellState.FieldStore.assign] at prefixExact
  change false = true at prefixExact
  cases prefixExact

/-- info: 'Minidregg.Assurance.CapabilityRevocationAudit.canonical_command_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonical_command_roundtrip
/-- info: 'Minidregg.Assurance.CapabilityRevocationAudit.revoked_parent_denies_every_verb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revoked_parent_denies_every_verb

end Minidregg.Assurance.CapabilityRevocationAudit
