/-
# Native semantic history verification

A physically self-consistent DataIntent log is not authority. Starting at the
operator-pinned genesis, each retained original signed ingress is admitted by
its real native receiver at the original prefix height. Only the intent emitted
by that accepted receiver may extend the verified prefix. Full canonical record
bytes are compared, including all posts, read guards, charges and receipt IDs.

This module never calls storage CAS or the replay-success fast path. The native
signature helper is the existing cryptographic execution boundary. Unknown old
wire versions and unsupported event families refuse rather than becoming opaque
trusted history. Profile/clock changes require an explicit future migration.
-/
import Kernel.NativeHostContext

namespace Minidregg.Kernel.NativeHostReplay

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost

set_option autoImplicit false
attribute [local irreducible] NativeHost.Config.profile CanonicalRuntimeProfile.Profile.compilerProfile

/-- Evidence is one of the actual privately admitted receiving objects,
not a supplied policy decision, signature Boolean, or arbitrary DataIntent. -/
inductive NativeAdmission (config : Config) (opened : Opened config) : DataIntent rootBytes → Prop
  | birth (accepted : ResourceBirthPolicyController.Concrete.AcceptedBirth
      config.profile config.deployment opened.pins opened.durable
      (logicalHeight config opened.durable)) :
      NativeAdmission config opened (ResourceBirthReceiver.intent accepted)
  | invoke {command : DeclaredResourceController.Command}
      (prepared : DeclaredResourceController.PreparedInvocation config.deployment config.profile
        ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable command)
      (signed : DeclaredResourceController.SignedCommand)
      (shape : DeclaredResourceController.PhysicalShape prepared)
      (accepted : DeclaredResourceController.AcceptedInvocation prepared signed) :
      NativeAdmission config opened (accepted.dataIntent shape)
  | install (accepted : PolicyInstallReceiver.AcceptedInstall config.profile config.deployment
      opened.durable config.federation (logicalHeight config opened.durable)) :
      NativeAdmission config opened (PolicyInstallReceiver.intent accepted)
  | delegate {ingress : CapabilityDelegationReceiver.DecodedIngress}
      (accepted : CapabilityDelegationReceiver.AcceptedDelegation config.deployment config.profile
        ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable ingress) :
      NativeAdmission config opened (CapabilityDelegationReceiver.intent accepted)
  | revoke {ingress : CapabilityRevocationReceiver.DecodedIngress}
      (accepted : CapabilityRevocationReceiver.AcceptedRevocation config.deployment config.profile
        ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable ingress) :
      NativeAdmission config opened (CapabilityRevocationReceiver.intent accepted)

structure Derived (config : Config) (opened : Opened config) where
  intent : DataIntent rootBytes
  admission : NativeAdmission config opened intent

/-- Fresh native admission is mandatory even if the final image contains an
identical receipt. Original keys, capabilities and source are read from this
verified prefix, and the original signed request is checked at its old height. -/
def derive (config : Config) (opened : Opened config) (bytes : List UInt8) :
    IO (Except String (Derived config opened)) := do
  let height := logicalHeight config opened.durable
  if let some ingress := CapabilityRevocationReceiver.decodeIngress bytes then
    match ← CapabilityRevocationReceiver.admitDecodedNative config.deployment config.profile
        ⟨config.federation, height⟩ opened.durable config.signature ingress with
    | .error reason => return .error s!"revocation refused: {repr reason}"
    | .ok accepted => return .ok ⟨CapabilityRevocationReceiver.intent accepted, .revoke accepted⟩
  match ResourceBirthPolicyController.Concrete.decodeIngress bytes with
  | some ingress =>
      match ← ResourceBirthPolicyController.Concrete.admitDecodedNative config.profile config.deployment
          opened.pins config.signature opened.durable height ingress with
      | .error reason => return .error s!"birth admission refused: {repr reason}"
      | .ok accepted => return .ok ⟨ResourceBirthReceiver.intent accepted, .birth accepted⟩
  | none =>
    match PolicyInstallReceiver.decodeIngress bytes with
    | some ingress =>
        match ← PolicyInstallReceiver.admitDecodedNative config.profile config.deployment config.signature
            opened.durable config.federation height ingress with
        | .error reason => return .error s!"policy installation refused: {repr reason}"
        | .ok accepted => return .ok ⟨PolicyInstallReceiver.intent accepted, .install accepted⟩
    | none =>
      match CapabilityDelegationReceiver.decodeIngress bytes with
      | some ingress =>
          match ← CapabilityDelegationReceiver.admitDecodedNative config.deployment config.profile
              ⟨config.federation, height⟩ opened.durable config.signature ingress with
          | .error reason => return .error s!"delegation refused: {repr reason}"
          | .ok accepted => return .ok ⟨CapabilityDelegationReceiver.intent accepted, .delegate accepted⟩
      | none =>
        match DeclaredResourceController.decodeSignedBytes bytes with
        | none => return .error "unsupported or noncanonical signed historical ingress"
        | some (domain, semantics, signed) =>
            if domain != config.deployment.domain || semantics != config.profile.semantics then
              return .error "historical invocation domain/profile mismatch"
            match DeclaredResourceController.commandCodec.decode signed.commandBytes with
            | none => return .error "noncanonical historical invocation command"
            | some command =>
              match DeclaredResourceController.prepare config.deployment config.profile
                  ⟨config.federation, height⟩ opened.durable command with
              | .error reason => return .error s!"invocation preparation refused: {repr reason}"
              | .ok prepared =>
                if shape : DeclaredResourceController.PhysicalShape prepared then
                  match ← DeclaredResourceController.admit config.signature prepared signed with
                  | .error reason => return .error s!"invocation admission refused: {repr reason}"
                  | .ok accepted => return .ok ⟨accepted.dataIntent shape,
                      .invoke prepared signed shape accepted⟩
                else return .error "historical invocation physical shape refused"

/-- Compare the complete existing canonical record codec. Function-valued
metering charges are serialized in all ten lanes by that codec. -/
def recordMatches (record : DurableReceiver.IntentRecord) (intent : DataIntent rootBytes) : Bool :=
  decide (DurableReceiverCodec.intentStream.encode record =
    DurableReceiverCodec.intentStream.encode (DurableReceiver.IntentRecord.ofIntent intent))

theorem recordMatches_iff (record : DurableReceiver.IntentRecord) (intent : DataIntent rootBytes) :
    recordMatches record intent = true ↔ record = DurableReceiver.IntentRecord.ofIntent intent := by
  simp only [recordMatches, decide_eq_true_eq]
  exact (lawful_encode_injective DurableReceiverCodec.intentStream.toLawful).eq_iff

/-- Byte equality does not stand in for a cryptographic collision assumption:
the stored record must be exactly the source-derived accepted record. -/
theorem matched_record_admitted {config : Config} {opened : Opened config}
    (derived : Derived config opened) (record : DurableReceiver.IntentRecord)
    (matched : recordMatches record derived.intent = true) :
    record = DurableReceiver.IntentRecord.ofIntent derived.intent ∧
      NativeAdmission config opened derived.intent :=
  ⟨(recordMatches_iff record derived.intent).mp matched, derived.admission⟩

/-- Advance through the same canonical durable executor using the derived
intent, never the untrusted stored post. This reuses its checked next snapshot
and append proof instead of replaying the whole physical prefix again. -/
def advance {config : Config} (opened : Opened config) (derived : Derived config opened) : Except String Durable :=
  match DurableReceiver.prepare opened.durable.image opened.durable.snapshot
      opened.durable.represented derived.intent with
  | .inl ready =>
      let image := opened.durable.image.append derived.intent
      .ok ⟨DurableReceiverCodec.encode image, image, ready.next, rfl, ready.restored⟩
  | .inr (.rejected reason) => .error s!"derived durable intent refused: {repr reason}"
  | .inr (.replayed _) => .error "duplicate accepted history entry"
  | .inr _ => .error "derived durable intent did not make one new commit"

structure Failure where
  /-- Zero-based failing accepted entry; genesis failures use zero too. -/
  index : Nat
  detail : String
  deriving Repr

private def walk (config : Config) (opened : Opened config)
    (receipts : List NativeHostCodec.Receipt) : List DurableReceiver.IntentRecord →
    IO (Except Failure (Opened config × List NativeHostCodec.Receipt))
  | [] => pure (.ok (opened, receipts.reverse))
  | record :: rest => do
      let index := opened.durable.image.accepted.length
      match ← derive config opened record.event.canonicalBytes with
      | .error detail => return .error ⟨index, detail⟩
      | .ok derived =>
        if !recordMatches record derived.intent then
          return .error ⟨index, "retained intent differs from native-admitted intent"⟩
        match advance opened derived with
        | .error detail => return .error ⟨index, detail⟩
        | .ok next =>
          match validateLoaded config next with
          | .error detail => return .error ⟨index, s!"native post image: {detail}"⟩
          | .ok validated =>
            let receipt : NativeHostCodec.Receipt :=
              ⟨derived.intent.transactionId, derived.intent.event.eventId,
                index + 1, imageBoundary config next.image⟩
            walk config validated (receipt :: receipts) rest

/-- Constructed only after all original ingresses are freshly native-admitted
at their prefixes and all exact expected records reconstruct the supplied tip.
Receipts are recomputed from those same expected prefix images. -/
structure Verified (config : Config) (target : Durable) where
  private mk ::
  opened : Opened config
  exactBytes : opened.durable.bytes = target.bytes
  receipts : List NativeHostCodec.Receipt
  countExact : receipts.length = target.image.accepted.length

/-- The final comparison binds the full finite image, not merely a digest or
its materialized state. No collision-resistance hypothesis is involved. -/
theorem Verified.image_exact {config : Config} {target : Durable}
    (verified : Verified config target) : verified.opened.durable.image = target.image := by
  apply DurableReceiverCodec.encode_injective
  rw [verified.opened.durable.canonical, target.canonical]
  exact verified.exactBytes

def verifyLoaded (config : Config) (target : Durable) : IO (Except Failure (Verified config target)) := do
  let genesis : DurableReceiver.Image := ⟨target.image.seed, []⟩
  match DurableReceiverIO.loadBytes rootBytes (DurableReceiverCodec.encode genesis) with
  | .error detail => return .error ⟨0, s!"genesis decoding: {detail}"⟩
  | .ok initial =>
    match validateLoaded config initial with
    | .error detail => return .error ⟨0, s!"pinned genesis: {detail}"⟩
    | .ok opened =>
      match ← walk config opened [] target.image.accepted with
      | .error failure => return .error failure
      | .ok (final, receipts) =>
        if exactBytes : final.durable.bytes = target.bytes then
          if countExact : receipts.length = target.image.accepted.length then
            return .ok ⟨final, exactBytes, receipts, countExact⟩
          else return .error ⟨target.image.accepted.length, "verified history count mismatch"⟩
        else return .error ⟨target.image.accepted.length, "verified canonical tip mismatch"⟩

/-- Read-only bytes entrypoint for independent verification. No storage driver
or network publication is called by this module. -/
def verifyBytes (config : Config) (bytes : List UInt8) : IO (Except Failure (Sigma (Verified config))) := do
  match DurableReceiverIO.loadBytes rootBytes bytes with
  | .error detail => return .error ⟨0, detail⟩
  | .ok target =>
    match ← verifyLoaded config target with
    | .error failure => return .error failure
    | .ok verified => return .ok ⟨target, verified⟩

end Minidregg.Kernel.NativeHostReplay
