/- Governed transfer preparation settles through ONE existing source CAS and
exact readback. In an agreed domain a real current-context checked quorum commit
must order this full source record. Replica-local journals never become source.
The phase model has later mandatory native/private producers; this receiver
currently exports preparation only and cannot activate from a callback/flag.
-/
import Kernel.PortableHomeTransferAdmission
import Kernel.NativeHostContext
import Compiler.GenericSimplexIO
import Compiler.PortableHomeSourceCutIO
import Compiler.PortableParticipantPinIO
namespace Minidregg.Kernel.PortableHomeTransferReceiver
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.PortableHomeTransferAdmission
set_option autoImplicit false

abbrev Consent (config : Config) (opened : Opened config) :=
  Prepared config.deployment config.profile
    ⟨config.federation,logicalHeight config opened.durable⟩ opened.durable

private def history (opened : Opened config) : List (List UInt8) :=
  opened.durable.image.accepted.map DurableReceiverIO.recordFrame.encode
private def payload (consent : Consent config opened) : List UInt8 :=
  DurableReceiverIO.recordFrame.encode (DurableReceiver.IntentRecord.ofIntent consent.intent)

structure Ordered (config : Config) (opened : Opened config) (consent : Consent config opened) where
  private mk ::
  expected : Context
  contextPinned : config.jointConsensus = some expected
  commit : VerifiedCommit expected
  sourcePrefix : (history opened ++ [payload consent]).IsPrefix (commit.block.filter (fun b => !b.isEmpty))

def order (config : Config) (opened : Opened config) (consent : Consent config opened)
    (expected : Context) (commit : VerifiedCommit expected) : Option (Ordered config opened consent) :=
  if pinned : config.jointConsensus = some expected then
    if exact : (history opened ++ [payload consent]).IsPrefix (commit.block.filter (fun b => !b.isEmpty)) then
      some ⟨expected,pinned,commit,exact⟩ else none
  else none

/-- Existing source facet laws remain load-bearing. Captain registration adds
portable's own control protection to ordinary/live/replay receiving; this precise
private exception is selected only after two actual current consent admissions.
The logical source generation/epoch is never learned from an archive flag. -/
private def transport (config : Config) (opened : Opened config) (consent : Consent config opened)
    (agreed : Bool) : DurableReceiverIO.Transport :=
  let underlying := if agreed then config.physicalTransport else config.transport
  {underlying with sourceGate := fun snapshot intent => do
    config.sourceGate none snapshot intent
    if DurableReceiverCodec.intentStream.encode (DurableReceiver.IntentRecord.ofIntent intent) !=
        DurableReceiverCodec.intentStream.encode (DurableReceiver.IntentRecord.ofIntent consent.intent) ||
        snapshot.canonicalBytes consent.pin.cell != opened.durable.snapshot.canonicalBytes consent.pin.cell then
      throw (.durable .transactionConflict)
    else pure ()}

structure Pending (config : Config) (archive : PortableContinuationArchiveIO.NativeConfig)
    (opened : Opened config) (consent : Consent config opened) where
  private mk ::
  custody : PortableHomeSourceCutIO.Captured config archive consent.pin
  exactCustody : PortableHomeSourceCutIO.reference custody = consent.plan.source
  participant : PortableParticipantPinIO.Config
  oldPin : PortableContinuationManifest.ParticipantPin
  acknowledged : PortableParticipantPinIO.Held participant oldPin custody.audited.manifest
  exactAcknowledgement : acknowledged.checked.next = consent.plan.acknowledged
  appended : DurableReceiverIO.Appended ResourceBirthCodec.rootBytes opened.durable consent.intent
  /-- A current-context commit is compulsory exactly when the source config is
  agreed. This field is opaque and cannot be reconstructed from a local journal. -/
  ordered : Option (Ordered config opened consent)
  agreement : config.jointConsensus.isSome = ordered.isSome

inductive Result (config : Config) (archive : PortableContinuationArchiveIO.NativeConfig)
    (opened : Opened config) (consent : Consent config opened) where
  | prepared (pending : Pending config archive opened consent)
  | refused
  | ordinary (result : DurableReceiverIO.Result ResourceBirthCodec.rootBytes)

/-- Archive readback is required at the actual source consumer, not merely in
an optional caller workflow. Exact source image/reference must match current
admission before the existing source CAS; reopen repairs/refuses stale chunks.
The source epoch transition still grants no physical private/worker activation. -/
def applyPrepared (config : Config) (archive : PortableContinuationArchiveIO.NativeConfig)
    (opened : Opened config) (consent : Consent config opened)
    (custody : PortableHomeSourceCutIO.Captured config archive consent.pin)
    (participant : PortableParticipantPinIO.Config) (oldPin : PortableContinuationManifest.ParticipantPin)
    (held : PortableParticipantPinIO.Held participant oldPin custody.audited.manifest)
    (ordered : Option (Ordered config opened consent)) : IO (Result config archive opened consent) := do
  if exactCustody : PortableHomeSourceCutIO.reference custody = consent.plan.source then
    if exactAcknowledgement : held.checked.next = consent.plan.acknowledged then
      match ← PortableParticipantPinIO.hold participant oldPin custody.audited.manifest held.checked with
      | .error _ => return .refused
      | .ok _ => pure ()
      if DurableReceiverCodec.encode custody.audited.source.target.image !=
          DurableReceiverCodec.encode opened.durable.image then return .refused
      match ← PortableContinuationArchiveIO.reopen archive custody.audited.manifest
          custody.readback.inventory custody.readback.exactInventory with
      | .error _ => return .refused
      | .ok _ => pure ()
      if identity : consent.plan.source.identity =
          ⟨config.deployment.domain,config.profile.semantics,config.expectedSeed⟩ then
        if agreement : config.jointConsensus.isSome = ordered.isSome then
          match ← DurableReceiverIO.receiveLoadedDetailed
              (transport config opened consent ordered.isSome)
              ResourceBirthCodec.rootBytes opened.durable consent.intent with
          | .exact _ appended => return .prepared ⟨custody,exactCustody,participant,oldPin,
              held,exactAcknowledgement,appended,ordered,agreement⟩
          | .ordinary result => return .ordinary result
        else return .refused
      else return .refused
    else return .refused
  else return .refused

theorem pending_source_image {config : Config} {archive : PortableContinuationArchiveIO.NativeConfig} {opened : Opened config}
    {consent : Consent config opened} (pending : Pending config archive opened consent) :
    pending.appended.next.image = opened.durable.image.append consent.intent := pending.appended.image

theorem pending_agreement {config : Config} {archive : PortableContinuationArchiveIO.NativeConfig} {opened : Opened config}
    {consent : Consent config opened} (pending : Pending config archive opened consent) :
    config.jointConsensus.isSome = pending.ordered.isSome := pending.agreement

#assert_axioms pending_source_image
#assert_axioms pending_agreement
end Minidregg.Kernel.PortableHomeTransferReceiver
