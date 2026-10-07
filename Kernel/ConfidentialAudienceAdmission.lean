/- Mandatory all-keyholder entitlement for exact resource views. The outer
controller owns provenance of `view` (validated post or current release source),
its current height, signed roster witness and final commit. No bytes are returned.
Initial device profile: one separate content registry, canonical atom 0 containing
exactly the complete entry list. Device-source writes in the same invocation are
refused until a source-owned final-overlay construction exists. -/
import Kernel.RecipientReadEntitlement
import Kernel.ObjectAudience
import Kernel.AudienceRosterBinding
namespace Minidregg.Kernel.ConfidentialAudienceAdmission
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false
abbrev Entry := Minidregg.Theory.ObjectAudienceRoster.Entry
abbrev Roster := Minidregg.Theory.ObjectAudienceRoster.Roster
abbrev Context := ResourceObservationAdmission.Context
abbrev Deployment := ResourceObservationAdmission.Deployment
abbrev Durable := ResourceObservationAdmission.Durable
abbrev Registry := CanonicalCellRegistry.registry
variable {F : Type} [Field F] [DecidableEq F]
variable {deployment : Deployment}
variable {profile : CanonicalRuntimeProfile.Profile F}

/-- Typed canonical device data must be present in a current authenticated
content resource; matching protected-object roots is not device validation. -/
abbrev devicePayload (context : Context deployment) (source : Nat) :=
  AudienceRosterBinding.catalogPayload context source

/-- Pure physical guards derived from signed roster source identifiers. Admission
checks each source's actual typed canonical payload before this list is used. -/
def rosterDeviceGuards (context : Context deployment) (roster : Roster) : List ReadGuard :=
  ((roster.entries.map fun entry => entry.deviceSource).eraseDups).map fun source =>
    ⟨⟨source⟩, context.view.model.roots ⟨source⟩⟩

def recipientRequest (context : Context deployment) (semantics : Digest)
    (ambient : DeclaredResourceController.Ambient) (object : Nat) (root : Digest)
    (roster : Roster) (entry : Entry) (disclosure : List UInt8) : Request .object where
  domain := deployment.domain
  semantics := semantics
  federation := ambient.federation
  subject := ⟨entry.subject⟩
  subjectKeyEpoch := context.authority.authState.subjectKeyEpoch ⟨entry.subject⟩
  target := ⟨object⟩
  verb := .observeObject
  argsDigest := (Sp800185Cshake256.hash "LOOM.AUDIENCE.READ.VIEW/v1".toUTF8.toList
    (ObjectAudienceRoster.encode roster ++ disclosure)).digest
  effectsDigest := (Sp800185Cshake256.hash "LOOM.AUDIENCE.READ.VIEW/v1".toUTF8.toList
    (ObjectAudienceRoster.encode roster ++ disclosure)).digest
  nonce := roster.transition
  height := ambient.height
  preStateRoot := root
  policyId := ⟨object⟩
  policyEpoch := context.authority.authState.policyEpoch ⟨object⟩
  policyRevision := context.authority.authState.policyRevision ⟨object⟩
  cost := (ObjectAudienceRoster.entryStream.encode entry).length

abbrev One (context : Context deployment) (ambient : DeclaredResourceController.Ambient)
    (object : Nat) (preRoot : Digest) (roster : Roster) (entry : Entry)
    (view : PackedCell Registry) (disclosure : List UInt8) :=
  Σ prepared : ResourceObservationAdmission.Prepared context profile
    (recipientRequest context profile.semantics ambient object preRoot roster entry disclosure)
    roster.transition ⟨entry.capability⟩ disclosure,
    RecipientReadEntitlement.CheckedView (ambient.height - context.height) prepared entry view

/-- All entries are checked; a failed/offline-holder entitlement cannot be
silently filtered out. Offline principals need no live query signature. -/
def checkOne (context : Context deployment) (ambient : DeclaredResourceController.Ambient)
    (object : Nat) (preRoot : Digest) (roster : Roster) (entry : Entry)
    (view : PackedCell Registry) (disclosure : List UInt8) : Option (One (profile := profile) context ambient object preRoot roster entry view disclosure) :=
  let wanted := recipientRequest context profile.semantics ambient object preRoot roster entry disclosure
  match ResourceObservationAdmission.prepare context profile wanted roster.transition
      ⟨entry.capability⟩ disclosure with
  | .error _ => none
  | .ok prepared =>
    match RecipientReadEntitlement.checkView (profile := profile) (context := context)
      (wanted := wanted) (marker := roster.transition) (capability := ⟨entry.capability⟩)
      (contextBytes := disclosure) (ambient.height - context.height) prepared entry view with
    | none => none
    | some checked => some ⟨prepared, checked⟩

def checkAll (context : Context deployment) (ambient : DeclaredResourceController.Ambient)
    (object : Nat) (preRoot : Digest) (roster : Roster) (view : PackedCell Registry) (disclosure : List UInt8) :
    (entries : List Entry) → Option ((entry : Entry) → entry ∈ entries →
      One (profile := profile) context ambient object preRoot roster entry view disclosure)
  | [] => some (by
      intro entry member
      have impossible : False := by simpa using member
      exact False.elim impossible)
  | head :: tail => do
      let here ← checkOne (profile := profile) context ambient object preRoot roster head view disclosure
      let later ← checkAll context ambient object preRoot roster view disclosure tail
      pure (by
        intro entry member
        by_cases same : entry = head
        · subst entry; exact here
        · exact later entry ((List.mem_cons.mp member).resolve_left same))

structure Checked (context : Context deployment) (ambient : DeclaredResourceController.Ambient)
    (object : Nat) (preRoot : Digest) (state : Minidregg.Theory.ObjectAudience.State) (roster : Roster)
    (view : PackedCell Registry) (disclosure : List UInt8) where
  private mk ::
  active : Minidregg.Theory.ObjectAudience.Fresh state object (some roster.epoch)
  bound : ObjectAudienceRoster.Bound state roster roster.entries
  source : Nat
  separate : source ≠ object
  registryPayload : Digest × List UInt8
  registryExact : devicePayload context source = some registryPayload
  recordsExact : registryPayload.2 = (StreamCodec.list ObjectAudienceRoster.entryStream).encode roster.entries
  sourcesExact : ∀ entry ∈ roster.entries, entry.deviceSource = source
  all : (entry : {e : Entry // e ∈ roster.entries}) → One (profile := profile) context ambient object preRoot roster entry.val view disclosure

/-- Guard roots derive from the same physical image as registry resolution.
The outer receiver must refuse writes to `checked.source` and protect authority,
clock/current policy source (ordinary DRC already guards the latter three). -/
def Checked.deviceGuard {context : Context deployment} {ambient : DeclaredResourceController.Ambient}
    {object : Nat} {preRoot : Digest} {state : Minidregg.Theory.ObjectAudience.State} {roster : Roster} {view : PackedCell Registry} {disclosure : List UInt8}
    (checked : Checked (profile := profile) context ambient object preRoot state roster view disclosure) : ReadGuard :=
  ⟨⟨checked.source⟩, context.view.model.roots ⟨checked.source⟩⟩

/-- These are the dependencies retained by the actual all-holder entitlement
witnesses, including ambient/kind law closures. The outer DRC must include this
list in final CAS; a device-only guard list is insufficient. -/
def Checked.readGuards {context : Context deployment} {ambient : DeclaredResourceController.Ambient}
    {object : Nat} {preRoot : Digest} {state : Minidregg.Theory.ObjectAudience.State} {roster : Roster}
    {view : PackedCell Registry} {disclosure : List UInt8}
    (checked : Checked (profile := profile) context ambient object preRoot state roster view disclosure) : List ReadGuard :=
  checked.deviceGuard :: roster.entries.attach.flatMap (fun entry => (checked.all entry).2.guards)

/-- One concrete receiving request, including source's current state metadata.
Its accepted result retains a witness for every entry, not an arbitrary Boolean. -/
def check (context : Context deployment) (ambient : DeclaredResourceController.Ambient)
    (object : Nat) (preRoot : Digest) (state : Minidregg.Theory.ObjectAudience.State) (roster : Roster)
    (view : PackedCell Registry) (disclosure : List UInt8) : Option (Checked (profile := profile) context ambient object preRoot state roster view disclosure) :=
  if active : Minidregg.Theory.ObjectAudience.Fresh state object (some roster.epoch) then
    if bound : ObjectAudienceRoster.Bound state roster roster.entries then
      match roster.entries.head? with
      | none => none
      | some entry =>
        let source := entry.deviceSource
        if separate : source ≠ object then
          match registryExact : devicePayload context source with
          | none => none
          | some registryPayload =>
            if recordsExact : registryPayload.2 = (StreamCodec.list ObjectAudienceRoster.entryStream).encode roster.entries then
             if sourcesExact : ∀ entry ∈ roster.entries, entry.deviceSource = source then
              match checkAll (profile := profile) context ambient object preRoot roster view disclosure roster.entries with
              | none => none
              | some all =>
                some ⟨active, bound, source, separate, registryPayload, registryExact, recordsExact, sourcesExact,
                  fun entry => all entry.val entry.property⟩
             else none
            else none
        else none
    else none
  else none
end Minidregg.Kernel.ConfidentialAudienceAdmission
