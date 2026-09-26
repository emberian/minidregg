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
open Minidregg.Compiler.Tower256ConcreteBackend
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

/-- One checked step of the real replay loop. Its derived value contains
`NativeAdmission`, so a stored record alone cannot witness this relation. -/
def AdmittedStep (config : Config) (before after : Opened config)
    (record : DurableReceiver.IntentRecord) (receipt : NativeHostCodec.Receipt) : Prop :=
  ∃ derived : Derived config before,
    recordMatches record derived.intent = true ∧
    ∃ next : Durable,
      advance before derived = .ok next ∧
      validateLoaded config next = .ok after ∧
      receipt = ⟨derived.intent.transactionId, derived.intent.event.eventId,
        before.durable.image.accepted.length + 1, imageBoundary config next.image⟩

/-- The ordered semantic history that `walk` actually constructs. -/
inductive AdmittedReplay (config : Config) : Opened config →
    List DurableReceiver.IntentRecord → Opened config →
    List NativeHostCodec.Receipt → Prop
  | nil (opened) : AdmittedReplay config opened [] opened []
  | cons {before middle after record records receipt receipts}
      (step : AdmittedStep config before middle record receipt)
      (tail : AdmittedReplay config middle records after receipts) :
      AdmittedReplay config before (record :: records) after (receipt :: receipts)

theorem AdmittedReplay.append {config : Config}
    {before middle after : Opened config}
    {prior later : List DurableReceiver.IntentRecord}
    {priorReceipts laterReceipts : List NativeHostCodec.Receipt}
    (left : AdmittedReplay config before prior middle priorReceipts)
    (right : AdmittedReplay config middle later after laterReceipts) :
    AdmittedReplay config before (prior ++ later) after
      (priorReceipts ++ laterReceipts) := by
  induction left with
  | nil _ => simpa using right
  | cons step tail ih =>
      simpa only [List.cons_append] using AdmittedReplay.cons step (ih right)

private structure Walked (config : Config) (start : Opened config)
    (records : List DurableReceiver.IntentRecord) where
  final : Opened config
  receipts : List NativeHostCodec.Receipt
  trace : AdmittedReplay config start records final receipts

private def walk (config : Config) (opened : Opened config) :
    (records : List DurableReceiver.IntentRecord) →
    IO (Except Failure (Walked config opened records))
  | [] => pure (.ok ⟨opened, [], .nil opened⟩)
  | record :: rest => do
      let index := opened.durable.image.accepted.length
      match ← derive config opened record.event.canonicalBytes with
      | .error detail => return .error ⟨index, detail⟩
      | .ok derived =>
        if matched : recordMatches record derived.intent = true then
          match advanced : advance opened derived with
          | .error detail => return .error ⟨index, detail⟩
          | .ok next =>
            match validated : validateLoaded config next with
            | .error detail => return .error ⟨index, s!"native post image: {detail}"⟩
            | .ok after =>
              let receipt : NativeHostCodec.Receipt :=
                ⟨derived.intent.transactionId, derived.intent.event.eventId,
                  index + 1, imageBoundary config next.image⟩
              match ← walk config after rest with
              | .error failure => return .error failure
              | .ok tail =>
                return .ok ⟨tail.final, receipt :: tail.receipts,
                  .cons ⟨derived, matched, next, advanced, validated, rfl⟩ tail.trace⟩
        else
          return .error ⟨index, "retained intent differs from native-admitted intent"⟩

/-- Constructed only after all original ingresses are freshly native-admitted
at their prefixes and all exact expected records reconstruct the supplied tip.
Receipts are recomputed from those same expected prefix images. -/
structure Verified (config : Config) (target : Durable) where
  private mk ::
  origin : Opened config
  opened : Opened config
  exactBytes : opened.durable.bytes = target.bytes
  receipts : List NativeHostCodec.Receipt
  countExact : receipts.length = target.image.accepted.length
  admitted : AdmittedReplay config origin target.image.accepted opened receipts

/-- The final comparison binds the full finite image, not merely a digest or
its materialized state. No collision-resistance hypothesis is involved. -/
theorem Verified.image_exact {config : Config} {target : Durable}
    (verified : Verified config target) : verified.opened.durable.image = target.image := by
  apply DurableReceiverCodec.encode_injective
  rw [verified.opened.durable.canonical, target.canonical]
  exact verified.exactBytes

/-- A successful operational verification carries every accepted transition,
including its original receipt, from the checked genesis to the exact tip. -/
theorem Verified.accepted_history {config : Config} {target : Durable}
    (verified : Verified config target) :
    AdmittedReplay config verified.origin target.image.accepted
      verified.opened verified.receipts :=
  verified.admitted

/-- An explicit semantic model of the native helper's verdicts. Physical
`derive` performs IO; a fixed pathname in `Config` does not make its result
stable. A session using this model must separately pin the verifier artifact
and execution environment, and establish that each actual invocation refines
the chosen verdict function. -/
abbrev VerifierSemantics (config : Config) :=
  (opened : Opened config) → (bytes : List UInt8) → Option (Derived config opened)

/-- One semantic transition uses the actual native-admission evidence and the
same durable advance and post-image validation as `walk`. The only abstraction
is the external helper verdict, supplied by `verifier`. -/
def SemanticStep (config : Config) (verifier : VerifierSemantics config)
    (before after : Opened config) (record : DurableReceiver.IntentRecord)
    (receipt : NativeHostCodec.Receipt) : Prop :=
  ∃ derived : Derived config before,
    verifier before record.event.canonicalBytes = some derived ∧
    recordMatches record derived.intent = true ∧
    ∃ next : Durable,
      advance before derived = .ok next ∧
      validateLoaded config next = .ok after ∧
      receipt = ⟨derived.intent.transactionId, derived.intent.event.eventId,
        before.durable.image.accepted.length + 1, imageBoundary config next.image⟩

/-- Ordered accepted-record replay with one original receipt per transition.
This is the pure trace of the operational `walk`, conditional on a stable
verifier semantics for its IO calls. -/
inductive SemanticReplay (config : Config) (verifier : VerifierSemantics config) :
    Opened config → List DurableReceiver.IntentRecord →
    Opened config → List NativeHostCodec.Receipt → Prop
  | nil (opened) : SemanticReplay config verifier opened [] opened []
  | cons {before middle after record records receipt receipts}
      (step : SemanticStep config verifier before middle record receipt)
      (tail : SemanticReplay config verifier middle records after receipts) :
      SemanticReplay config verifier before (record :: records) after (receipt :: receipts)

/-- Replay of an already checked prefix and a freshly checked suffix is the
same ordered semantic trace as replaying their concatenation. No IO theorem is
claimed: relating two native runs additionally requires a stable verifier
semantics and availability of the helper in the fresh run. -/
theorem SemanticReplay.append {config : Config} {verifier : VerifierSemantics config}
    {before middle after : Opened config}
    {prior later : List DurableReceiver.IntentRecord}
    {priorReceipts laterReceipts : List NativeHostCodec.Receipt}
    (left : SemanticReplay config verifier before prior middle priorReceipts)
    (right : SemanticReplay config verifier middle later after laterReceipts) :
    SemanticReplay config verifier before (prior ++ later) after
      (priorReceipts ++ laterReceipts) := by
  induction left with
  | nil _ => simpa using right
  | cons step tail ih =>
      simpa only [List.cons_append] using SemanticReplay.cons step (ih right)

/-- Two runs admit the same semantic steps if their verifier meanings agree
at each prefix. The operational native-helper refinement is a separate
physical premise, not a theorem of Lean's `IO`. -/
theorem SemanticReplay.verifier_congr {config : Config}
    {first second : VerifierSemantics config}
    (stable : ∀ opened bytes, first opened bytes = second opened bytes)
    {before after : Opened config}
    {records : List DurableReceiver.IntentRecord}
    {receipts : List NativeHostCodec.Receipt}
    (trace : SemanticReplay config first before records after receipts) :
    SemanticReplay config second before records after receipts := by
  induction trace with
  | nil opened => exact .nil opened
  | cons step tail ih =>
      rcases step with ⟨derived, verdict, matched, next, advanced, validated, receipt⟩
      exact .cons ⟨derived, (stable _ _).symm ▸ verdict, matched,
        next, advanced, validated, receipt⟩ ih

/-- Cached-prefix and fresh-suffix traces compose when both native runs
refine the same verifier meaning at every historical prefix. This statement
does not assume that a later helper launch is available; that is a separate
operational requirement for comparing IO outcomes. -/
theorem SemanticReplay.append_stable {config : Config}
    {cached fresh : VerifierSemantics config}
    (stable : ∀ opened bytes, cached opened bytes = fresh opened bytes)
    {before middle after : Opened config}
    {prior later : List DurableReceiver.IntentRecord}
    {priorReceipts laterReceipts : List NativeHostCodec.Receipt}
    (left : SemanticReplay config cached before prior middle priorReceipts)
    (right : SemanticReplay config fresh middle later after laterReceipts) :
    SemanticReplay config fresh before (prior ++ later) after
      (priorReceipts ++ laterReceipts) :=
  (left.verifier_congr stable).append right

def verifyLoaded (config : Config) (target : Durable) : IO (Except Failure (Verified config target)) := do
  let genesis : DurableReceiver.Image := ⟨target.image.seed, []⟩
  match DurableReceiverIO.loadBytes rootBytes (DurableReceiverCodec.encode genesis) with
  | .error detail => return .error ⟨0, s!"genesis decoding: {detail}"⟩
  | .ok initial =>
    match validateLoaded config initial with
    | .error detail => return .error ⟨0, s!"pinned genesis: {detail}"⟩
    | .ok opened =>
      match ← walk config opened target.image.accepted with
      | .error failure => return .error failure
      | .ok walked =>
        if exactBytes : walked.final.durable.bytes = target.bytes then
          if countExact : walked.receipts.length = target.image.accepted.length then
            return .ok ⟨opened, walked.final, exactBytes, walked.receipts,
              countExact, walked.trace⟩
          else return .error ⟨target.image.accepted.length, "verified history count mismatch"⟩
        else return .error ⟨target.image.accepted.length, "verified canonical tip mismatch"⟩

/-- Continue from a previously verified exact tip after an external read.
The full canonical seed and every prior accepted record must be identical;
rollback or rewriting cannot be treated as an append. Only the new suffix is
freshly admitted at its original heights. The final exact-byte check binds
the reconstructed image to the entire physical readback. -/
def extendVerified (config : Config) {oldTarget : Durable}
    (old : Verified config oldTarget) (target : Durable) :
    IO (Except Failure (Verified config target)) := do
  let count := oldTarget.image.accepted.length
  if !(DurableReceiverCodec.seedStream.encode target.image.seed ==
      DurableReceiverCodec.seedStream.encode oldTarget.image.seed) then
    return .error ⟨count, "verified genesis seed changed"⟩
  if target.image.accepted.length < count then
    return .error ⟨target.image.accepted.length, "verified history rolled back"⟩
  if prefixBytes : (StreamCodec.list DurableReceiverCodec.intentStream).encode
      (target.image.accepted.take count) =
      (StreamCodec.list DurableReceiverCodec.intentStream).encode
        oldTarget.image.accepted then
    let suffix := target.image.accepted.drop count
    match ← walk config old.opened suffix with
    | .error failure => return .error failure
    | .ok walked =>
      if exactBytes : walked.final.durable.bytes = target.bytes then
        let receipts := old.receipts ++ walked.receipts
        if countExact : receipts.length = target.image.accepted.length then
          have prefixExact : target.image.accepted.take count =
              oldTarget.image.accepted :=
            (lawful_encode_injective
              (StreamCodec.list DurableReceiverCodec.intentStream).toLawful) prefixBytes
          have acceptedExact : target.image.accepted = oldTarget.image.accepted ++ suffix := by
            calc
              target.image.accepted =
                  target.image.accepted.take count ++ target.image.accepted.drop count :=
                (List.take_append_drop count target.image.accepted).symm
              _ = oldTarget.image.accepted ++ suffix := by rw [prefixExact]
          have admitted : AdmittedReplay config old.origin target.image.accepted
              walked.final receipts := by
            rw [acceptedExact]
            exact old.admitted.append walked.trace
          return .ok ⟨old.origin, walked.final, exactBytes, receipts, countExact, admitted⟩
        else return .error ⟨target.image.accepted.length, "verified history count mismatch"⟩
      else return .error ⟨target.image.accepted.length, "verified canonical tip mismatch"⟩
  else
    return .error ⟨count, "verified accepted-record prefix changed"⟩

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

#print axioms Minidregg.Kernel.NativeHostReplay.AdmittedReplay.append
#print axioms Minidregg.Kernel.NativeHostReplay.Verified.accepted_history
#print axioms Minidregg.Kernel.NativeHostReplay.SemanticReplay.append_stable
