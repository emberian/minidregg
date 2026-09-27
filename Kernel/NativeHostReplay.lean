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
import Kernel.GrainResourceBirthReceiver
import Kernel.FnSelectiveReleaseAdmission
import Kernel.FnSelectiveReleaseSourceReceiver
import Kernel.ApplicationLifecycleBeginReceiver
import Kernel.ApplicationLifecycleClaimCore
import Kernel.ApplicationLifecycleClaimV2Core
import Kernel.ApplicationShareIssueReceiver
import Kernel.ApplicationShareIssueGrainReceiver
import Kernel.ApplicationAgentLifetimeGrantIntentTemplate
import Kernel.ApplicationAgentLifetimeDispatchCore
import Kernel.ApplicationDispatchHistoricalCore
import Kernel.ApplicationDispatchAgentCore
import Kernel.FnConsumerFrontierReplay
import Kernel.FnConsumerNamespaceAdmissionAt
import Kernel.FnConsumerNamespaceHistory
import Kernel.FnSelectedPollReleaseShape
import Kernel.FnSelectedPollAdmissionAt
import Kernel.FnEmptyPollAdmissionAtV2
import Kernel.ApplicationLifecycleCompletionCore
import Kernel.ApplicationLifecycleBeginV3Admission
import Kernel.ApplicationLifecycleClaimV3Core
import Kernel.ApplicationLifecycleCompletionV2Core
import Kernel.ApplicationLifecycleCreatedHistory

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

/-- An issue certificate is retained only after the replay walk has admitted
its original command, matched its complete durable record, and validated the
next physical image. The index records where that step entered the history. -/
structure PriorIssue (config : Config) where
  private mk ::
  index : Nat
  receipt : NativeHostCodec.Receipt
  evidence : ApplicationDispatchHistoricalCore.IssuedEvidence config

/-- An original ordinary invocation is retained as compact reserve-eligible
evidence only after its same-walk native admission, full record/receipt match,
advance, and successor validation. Its v2 context is unknown at that earlier
step; event21 later binds the actual signed nonce and exact reserve target. -/
structure PriorDispatchReserve (config : Config) where
  private mk ::
  index : Nat
  raw : ApplicationDispatchAgentReserveCore.RawEvidence config

/-- The admitted suffix has no write to this purse cell. A final-value-only
comparison would admit settlement followed by a reserve that restores the
same state; the full verified record suffix is examined instead. -/
def dispatchPurseUntouched (records : List DurableReceiver.IntentRecord)
    (task : Nat) : Prop :=
  records.all (fun record =>
    !decide (⟨task⟩ ∈ record.writes.map DataWrite.cellId)) = true

instance (records : List DurableReceiver.IntentRecord) (task : Nat) :
    Decidable (dispatchPurseUntouched records task) := by
  unfold dispatchPurseUntouched
  infer_instance

/-- A BEGIN enters this compact chronological context only after its complete
record has been admitted, advanced and validated by the replay walk. The
original Opened value is existential proof data, not a retained physical
prefix image. A later claim must independently reconstruct and re-admit that
exact prefix before it can use this certificate. -/
structure PriorBegin (config : Config) where
  private mk ::
  index : Nat
  ingress : ApplicationLifecycleBeginIngress.Ingress
  record : DurableReceiver.IntentRecord
  admitted : ∃ original : Opened config,
    ∃ accepted : ApplicationLifecycleBeginReceiver.Accepted config.deployment config.profile
      ⟨config.federation, logicalHeight config original.durable⟩ original.durable ingress,
      record = DurableReceiver.IntentRecord.ofIntent accepted.intent

/-- The v2 descriptor-bound BEGIN is retained separately from the historical
v1 grammar. A v2 claim cannot select a v1 pending record. -/
structure PriorBeginV2 (config : Config) where
  private mk ::
  index : Nat
  ingress : ApplicationLifecycleBeginV2Ingress.Ingress
  record : DurableReceiver.IntentRecord
  admitted : ∃ original : Opened config,
    ∃ accepted : ApplicationLifecycleBeginV2Admission.Accepted
      config.deployment config.profile
      ⟨config.federation, logicalHeight config original.durable⟩
      original.durable ingress,
      record = DurableReceiver.IntentRecord.ofIntent accepted.intent

/-- Compact selected-release evidence retained only after the same replay
walk has admitted the original event13, matched its full durable record, and
validated the successor. A later event17 must recheck its exact shape. -/
structure PriorSelectedRelease where
  private mk ::
  record : DurableReceiver.IntentRecord
  receipt : NativeHostCodec.Receipt

private def selectedReleaseFor (config : Config) (opened : Opened config)
    (releases : List PriorSelectedRelease) (key : Digest) :
    Option FnSelectedPollReleaseShape.Original :=
  releases.findSome? fun prior =>
    FnSelectedPollReleaseShape.selectAt config opened prior.record prior.receipt key

/-- A source-rechecked claim of a BEGIN that is present in the privately
admitted chronological context of this exact opened image. -/
structure ClaimAt (config : Config) (opened : Opened config)
    (ingress : ApplicationLifecycleClaimIngress.Ingress) where
  private mk ::
  prior : PriorBegin config
  indexExact : prior.index = ingress.source.originalIndex
  ingressExact : prior.ingress = ingress.source.begin
  present : opened.durable.image.accepted[prior.index]? = some prior.record
  conditional : ApplicationLifecycleClaimCore.Conditional config opened ingress
  recordExact : prior.record =
    DurableReceiver.IntentRecord.ofIntent conditional.original.admitted.intent

structure ClaimAtV2 (config : Config) (opened : Opened config)
    (ingress : ApplicationLifecycleClaimV2Ingress.Ingress) where
  private mk ::
  prior : PriorBeginV2 config
  indexExact : prior.index = ingress.base.source.originalIndex
  ingressExact : prior.ingress = ingress.originalBegin
  present : opened.durable.image.accepted[prior.index]? = some prior.record
  conditional : ApplicationLifecycleClaimV2Core.Conditional config opened ingress
  recordExact : prior.record =
    DurableReceiver.IntentRecord.ofIntent conditional.originalAccepted.intent

/-- A successful create completion is retained only after the complete
event-25 record and post-image were admitted by this walk. -/
structure PriorCreatedV3 (config : Config) where
  private mk ::
  index : Nat
  receipt : NativeHostCodec.Receipt
  ingress : ApplicationLifecycleCompletionV2Ingress.Ingress
  record : DurableReceiver.IntentRecord
  created : ingress.creationMarker.isSome = true
  admitted : ∃ original : Opened config,
    ∃ accepted : ApplicationLifecycleCompletionV2Admission.Candidate config original ingress,
      record = DurableReceiver.IntentRecord.ofIntent
        (ApplicationLifecycleCompletionV2Core.intent accepted)

/-- A physical running incarnation is retained only after the exact event25
record and successor image were admitted by this verified replay walk. STOP
must select this unit, invocation and cgroup; its own operation generation is
not the generation of the process being stopped. -/
structure PriorRunningV3 (config : Config) where
  private mk ::
  index : Nat
  receipt : NativeHostCodec.Receipt
  ingress : ApplicationLifecycleCompletionV2Ingress.Ingress
  record : DurableReceiver.IntentRecord
  running : ingress.source.physical.report.outcome = .running
  started : ingress.source.originalBegin.base.source.kind = .start
  admitted : ∃ original : Opened config,
    ∃ accepted : ApplicationLifecycleCompletionV2Admission.Candidate config original ingress,
      record = DurableReceiver.IntentRecord.ofIntent
        (ApplicationLifecycleCompletionV2Core.intent accepted)

structure RunningAt (config : Config) (opened : Opened config)
    (source : ApplicationLifecycleBegin.Source) where
  private mk ::
  prior : PriorRunningV3 config
  present : opened.durable.image.accepted[prior.index]? = some prior.record
  appExact : prior.ingress.source.originalBegin.base.source.app = source.app
  generationExact :
    prior.ingress.source.originalBegin.base.source.processGeneration =
      source.before.generation
  unitExact : prior.ingress.source.physical.report.unit = source.processIdentity
  imageExact : prior.ingress.source.physical.report.materializedImage =
    source.imageIdentity

/-- A completed-create candidate is usable only when its original event25 was
also admitted by the very replay walk that verified today's tip. -/
structure CreatedAt (config : Config) (opened : Opened config)
    (binding : ApplicationLifecycleLaunchBinding.Binding) where
  private mk ::
  prior : PriorCreatedV3 config
  selected : ApplicationLifecycleCreatedHistory.Candidate config opened binding
  indexExact : prior.index = selected.index
  receiptExact : prior.receipt = selected.receipt
  ingressExact : prior.ingress = selected.ingress
  recordExact : prior.record = selected.selected.record
  present : opened.durable.image.accepted[prior.index]? = some prior.record

/-- The chronology required by the signed BEGIN choice is retained as data,
including the original completed-create witness for every continue. -/
inductive BeginV3History (config : Config) (opened : Opened config)
    (ingress : ApplicationLifecycleBeginV3Ingress.Ingress) : Type where
  | install (selected : ingress.start = none)
  | stop (selected : ingress.start = none)
      (kind : ingress.base.source.kind = .stop)
      (running : RunningAt config opened ingress.base.source)
  | create (binding : ApplicationLifecycleLaunchBinding.Binding) (index : Nat)
      (selected : ingress.start = some binding)
      (choice : binding.choice = .create index)
  | continue (binding : ApplicationLifecycleLaunchBinding.Binding)
      (selected : ingress.start = some binding)
      (choice : binding.choice = .continue)
      (created : CreatedAt config opened binding)

structure BeginAtV3 (config : Config) (opened : Opened config)
    (ingress : ApplicationLifecycleBeginV3Ingress.Ingress) where
  private mk ::
  accepted : ApplicationLifecycleBeginV3Admission.Accepted
    config.deployment config.profile
    ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable ingress
  history : BeginV3History config opened ingress

def BeginAtV3.intent {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleBeginV3Ingress.Ingress}
    (admitted : BeginAtV3 config opened ingress) : DataIntent rootBytes :=
  admitted.accepted.intent

/-- A launch-bound BEGIN enters the verified chronology only after its full
event-23 intent, physical record, and successor image have matched. -/
structure PriorBeginV3 (config : Config) where
  private mk ::
  index : Nat
  ingress : ApplicationLifecycleBeginV3Ingress.Ingress
  record : DurableReceiver.IntentRecord
  admitted : ∃ original : Opened config,
    ∃ accepted : BeginAtV3 config original ingress,
      record = DurableReceiver.IntentRecord.ofIntent accepted.intent

structure ClaimAtV3 (config : Config) (opened : Opened config)
    (ingress : ApplicationLifecycleClaimV3Ingress.Ingress) where
  private mk ::
  prior : PriorBeginV3 config
  indexExact : prior.index = ingress.base.source.originalIndex
  ingressExact : prior.ingress = ingress.originalBegin
  present : opened.durable.image.accepted[prior.index]? = some prior.record
  conditional : ApplicationLifecycleClaimV3Core.Conditional config opened ingress
  recordExact : prior.record =
    DurableReceiver.IntentRecord.ofIntent conditional.originalAccepted.intent

def ClaimAtV3.intent {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleClaimV3Ingress.Ingress}
    (admitted : ClaimAtV3 config opened ingress) : DataIntent rootBytes :=
  admitted.conditional.intent

structure PriorClaimV3 (config : Config) where
  private mk ::
  index : Nat
  ingress : ApplicationLifecycleClaimV3Ingress.Ingress
  record : DurableReceiver.IntentRecord
  admitted : ∃ original : Opened config,
    ∃ accepted : ClaimAtV3 config original ingress,
      record = DurableReceiver.IntentRecord.ofIntent accepted.intent

private def selectCreatedAt (config : Config) (opened : Opened config)
    (created : List (PriorCreatedV3 config))
    (binding : ApplicationLifecycleLaunchBinding.Binding) :
    IO (Except String (CreatedAt config opened binding)) := do
  let selected ← match ← ApplicationLifecycleCreatedHistory.select config opened binding with
    | .error detail => return .error detail
    | .ok candidate => pure candidate
  let some prior := created.find? (fun prior =>
      prior.index == selected.index && prior.receipt == selected.receipt)
    | return .error "completed create absent from admitted replay chronology"
  if indexExact : prior.index = selected.index then
    if receiptExact : prior.receipt = selected.receipt then
      if ingressExact : prior.ingress = selected.ingress then
        if bytesExact : DurableReceiverCodec.intentStream.encode prior.record =
            DurableReceiverCodec.intentStream.encode selected.selected.record then
          have recordExact : prior.record = selected.selected.record :=
            (lawful_encode_injective DurableReceiverCodec.intentStream.toLawful) bytesExact
          have present : opened.durable.image.accepted[prior.index]? = some prior.record := by
            rw [indexExact, recordExact]
            exact selected.selected.atIndex
          return .ok ⟨prior, selected, indexExact, receiptExact, ingressExact,
            recordExact, present⟩
        else return .error "completed-create full record differs from admitted history"
      else return .error "completed-create ingress differs from admitted history"
    else return .error "completed-create receipt differs from admitted history"
  else return .error "completed-create index differs from admitted history"

private def selectRunningAt {config : Config} (opened : Opened config)
    (running : List (PriorRunningV3 config))
    (source : ApplicationLifecycleBegin.Source) :
    Except String (RunningAt config opened source) := do
  -- The list is newest first. Selecting by app before checking generation
  -- prevents an old running incarnation from being revived after a newer run.
  let some prior := running.find? (fun prior =>
      prior.ingress.source.originalBegin.base.source.app == source.app)
    | throw "STOP has no admitted running incarnation at current generation"
  match found : opened.durable.image.accepted[prior.index]? with
  | none => throw "STOP running completion record absent from verified prefix"
  | some record =>
      if bytesExact : DurableReceiverCodec.intentStream.encode record =
          DurableReceiverCodec.intentStream.encode prior.record then
        have recordExact : record = prior.record :=
          (lawful_encode_injective DurableReceiverCodec.intentStream.toLawful) bytesExact
        have present : opened.durable.image.accepted[prior.index]? = some prior.record := by
          rw [found, recordExact]
        if appExact : prior.ingress.source.originalBegin.base.source.app = source.app then
          if generationExact :
              prior.ingress.source.originalBegin.base.source.processGeneration =
                source.before.generation then
            if unitExact : prior.ingress.source.physical.report.unit = source.processIdentity then
              if imageExact : prior.ingress.source.physical.report.materializedImage =
                  source.imageIdentity then
                return ⟨prior, present, appExact, generationExact, unitExact, imageExact⟩
              else throw "STOP image differs from admitted running incarnation"
            else throw "STOP unit differs from admitted running incarnation"
          else throw "STOP generation differs from admitted running incarnation"
        else throw "STOP app differs from admitted running incarnation"
      else throw "STOP running completion record differs from verified prefix"

private def admitBeginV3At (config : Config) (opened : Opened config)
    (created : List (PriorCreatedV3 config))
    (running : List (PriorRunningV3 config))
    (ingress : ApplicationLifecycleBeginV3Ingress.Ingress) :
    IO (Except String (BeginAtV3 config opened ingress)) := do
  let history : BeginV3History config opened ingress ←
    match selected : ingress.start with
    | none =>
        if kind : ingress.base.source.kind = .stop then
          match selectRunningAt opened running ingress.base.source with
          | .error detail => return .error detail
          | .ok exact => pure (.stop selected kind exact)
        else pure (.install selected)
    | some binding =>
        match choice : binding.choice with
        | .create index => pure (.create binding index selected choice)
        | .continue =>
            match ← selectCreatedAt config opened created binding with
            | .error detail => return .error detail
            | .ok exact => pure (.continue binding selected choice exact)
  let ambient : DeclaredResourceController.Ambient :=
    ⟨config.federation, logicalHeight config opened.durable⟩
  match ← ApplicationLifecycleBeginV3Admission.admitNative config.deployment
      config.profile ambient config.signature opened.durable ingress with
  | .error detail => return .error detail
  | .ok accepted => return .ok ⟨accepted, history⟩

/-- A v2 claim joins this compact context only after the same replay walk
admitted its original command, matched the full record, advanced, and
validated the successor. Completion cannot select a merely structural claim
record from a caller-supplied Store. -/
structure PriorClaimV2 (config : Config) where
  private mk ::
  index : Nat
  ingress : ApplicationLifecycleClaimV2Ingress.Ingress
  record : DurableReceiver.IntentRecord
  admitted : ∃ original : Opened config,
    ∃ accepted : ClaimAtV2 config original ingress,
      record = DurableReceiver.IntentRecord.ofIntent accepted.conditional.intent

def ClaimAtV2.intent {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleClaimV2Ingress.Ingress}
    (admitted : ClaimAtV2 config opened ingress) : DataIntent rootBytes :=
  admitted.conditional.intent

theorem ClaimAtV2.original_record_at {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleClaimV2Ingress.Ingress}
    (admitted : ClaimAtV2 config opened ingress) :
    opened.durable.image.accepted[ingress.base.source.originalIndex]? =
      some (DurableReceiver.IntentRecord.ofIntent
        admitted.conditional.originalAccepted.intent) := by
  calc
    opened.durable.image.accepted[ingress.base.source.originalIndex]? =
        opened.durable.image.accepted[admitted.prior.index]? :=
      congrArg (fun index => opened.durable.image.accepted[index]?)
        admitted.indexExact.symm
    _ = some (DurableReceiver.IntentRecord.ofIntent
          admitted.conditional.originalAccepted.intent) := by
      rw [admitted.present, admitted.recordExact]

theorem ClaimAtV2.event_version {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleClaimV2Ingress.Ingress}
    (admitted : ClaimAtV2 config opened ingress) :
    admitted.intent.event.codecVersion = 16 := by
  change admitted.conditional.intent.event.codecVersion = 16
  rw [admitted.conditional.intent_event]
  rfl

/-- A completion is source-admitted only after its structural original-claim
candidate is matched to a claim retained by this same admitted replay walk.
The original claim's full record and canonical ingress are both compared. -/
structure CompletionAt (config : Config) (opened : Opened config)
    (ingress : ApplicationLifecycleCompletionIngress.Ingress) where
  private mk ::
  prior : PriorClaimV2 config
  conditional : ApplicationLifecycleCompletionAdmission.Candidate config opened ingress
  indexExact : prior.index = conditional.historical.index
  ingressExact : prior.ingress = ingress.source.originalClaim
  recordExact : prior.record = conditional.historical.selected.record
  present : opened.durable.image.accepted[prior.index]? = some prior.record

def CompletionAt.intent {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (admitted : CompletionAt config opened ingress) : DataIntent rootBytes :=
  ApplicationLifecycleCompletionCore.intent admitted.conditional

inductive CompletionV2Running (config : Config) (opened : Opened config)
    (ingress : ApplicationLifecycleCompletionV2Ingress.Ingress) : Type where
  | other (notStop : ingress.source.originalBegin.base.source.kind ≠ .stop)
  | stop (running : RunningAt config opened
        ingress.source.originalBegin.base.source)
      (unitExact : ingress.source.physical.report.unit =
        running.prior.ingress.source.physical.report.unit)
      (invocationExact : ingress.source.physical.report.invocationId =
        running.prior.ingress.source.physical.report.invocationId)
      (controlGroupExact : ingress.source.physical.report.controlGroup =
        running.prior.ingress.source.physical.report.controlGroup)
      (custodyExact : ingress.source.physical.report.volumeCustody =
        running.prior.ingress.source.physical.report.volumeCustody)

structure CompletionAtV2 (config : Config) (opened : Opened config)
    (ingress : ApplicationLifecycleCompletionV2Ingress.Ingress) where
  private mk ::
  prior : PriorClaimV3 config
  conditional : ApplicationLifecycleCompletionV2Admission.Candidate config opened ingress
  indexExact : prior.index = conditional.historical.index
  ingressExact : prior.ingress = ingress.source.originalClaim
  recordExact : prior.record = conditional.historical.selected.record
  present : opened.durable.image.accepted[prior.index]? = some prior.record
  running : CompletionV2Running config opened ingress

def CompletionAtV2.intent {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
    (admitted : CompletionAtV2 config opened ingress) : DataIntent rootBytes :=
  ApplicationLifecycleCompletionV2Core.intent admitted.conditional


theorem CompletionAt.original_claim_record_at {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (admitted : CompletionAt config opened ingress) :
    opened.durable.image.accepted[admitted.conditional.historical.index]? =
      some (DurableReceiver.IntentRecord.ofIntent
        admitted.conditional.historical.accepted.intent) := by
  calc
    opened.durable.image.accepted[admitted.conditional.historical.index]? =
        opened.durable.image.accepted[admitted.prior.index]? := by
          rw [admitted.indexExact]
    _ = some admitted.prior.record := admitted.present
    _ = some admitted.conditional.historical.selected.record := by
      rw [admitted.recordExact]
    _ = some (DurableReceiver.IntentRecord.ofIntent
          admitted.conditional.historical.accepted.intent) := by
      rw [admitted.conditional.historical.recordExact]

theorem CompletionAt.event_version {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (admitted : CompletionAt config opened ingress) :
    admitted.intent.event.codecVersion = 18 :=
  ApplicationLifecycleCompletionCore.intent_event_version admitted.conditional

def ClaimAt.intent {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleClaimIngress.Ingress}
    (admitted : ClaimAt config opened ingress) : DataIntent rootBytes :=
  admitted.conditional.intent

theorem ClaimAt.original_record_at {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleClaimIngress.Ingress}
    (admitted : ClaimAt config opened ingress) :
    opened.durable.image.accepted[ingress.source.originalIndex]? =
      some (DurableReceiver.IntentRecord.ofIntent
        admitted.conditional.original.admitted.intent) := by
  calc
    opened.durable.image.accepted[ingress.source.originalIndex]? =
        opened.durable.image.accepted[admitted.prior.index]? :=
      congrArg (fun index => opened.durable.image.accepted[index]?)
        admitted.indexExact.symm
    _ = some (DurableReceiver.IntentRecord.ofIntent
          admitted.conditional.original.admitted.intent) := by
      rw [admitted.present, admitted.recordExact]

theorem ClaimAt.event_version {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleClaimIngress.Ingress}
    (admitted : ClaimAt config opened ingress) :
    admitted.intent.event.codecVersion = 16 := by
  change admitted.conditional.intent.event.codecVersion = 16
  rw [admitted.conditional.intent_event]
  rfl

/-- A dispatch-specific current admission paired with a prior issue from the
same verified history. The private constructor prevents callers from supplying
an unrelated issue merely because its signed bytes decode. -/
structure DispatchAt (config : Config) (opened : Opened config)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) where
  private mk ::
  prior : PriorIssue config
  present : opened.durable.image.accepted[prior.index]? = some prior.evidence.record
  checked : ApplicationDispatchHistoricalCore.CheckedCandidate config opened.durable
    ingress prior.evidence

def DispatchAt.intent {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : DispatchAt config opened ingress) : DataIntent rootBytes :=
  ApplicationDispatchPending.candidateIntent admitted.checked.checked

theorem DispatchAt.event_full_ingress {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : DispatchAt config opened ingress) :
    admitted.intent.event.canonicalBytes = ingress.canonicalBytes :=
  ApplicationDispatchPending.candidateIntent_retains_full_ingress admitted.checked.checked

theorem DispatchAt.event_version {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : DispatchAt config opened ingress) :
    admitted.intent.event.codecVersion = 11 :=
  ApplicationDispatchPending.candidateIntent_event_version admitted.checked.checked

/-- Event27 joins a verified original event22 ticket issue to a fresh grant
birth and current signed app delegation on this same opened image. The old
ticket's parent generation is provenance, never the new execution witness. -/
structure LifetimeGrantIssueAt (config : Config) (opened : Opened config)
    (ingress : ApplicationAgentLifetimeGrantSource.Ingress) where
  private mk ::
  prior : PriorIssue config
  originalEvent22 : prior.evidence.record.event.codecVersion = 22
  originalIndex : prior.index = ingress.spec.grant.source.issueIndex
  originalReceipt : prior.receipt = ingress.spec.grant.source.issueReceipt
  present : opened.durable.image.accepted[prior.index]? = some prior.evidence.record
  scope : ingress.spec.grant.matchesIssued prior.evidence.spec prior.index prior.receipt = true
  current : ApplicationAgentLifetimeGrantAdmission.Accepted config.profile config
    opened.pins opened.durable (logicalHeight config opened.durable) ingress

def LifetimeGrantIssueAt.intent {config : Config} {opened : Opened config}
    {ingress : ApplicationAgentLifetimeGrantSource.Ingress}
    (admitted : LifetimeGrantIssueAt config opened ingress) : DataIntent rootBytes :=
  ApplicationAgentLifetimeGrantIntentTemplate.template admitted.current

/-- Event27 grant authority is retained only after its complete source intent,
record, receipt and successor were checked by this same history walk. The
physical content root comes from the source-derived initialized birth write,
never from a caller's current-root assertion. -/
structure PriorLifetimeGrant (config : Config) where
  private mk ::
  index : Nat
  receipt : NativeHostCodec.Receipt
  ingress : ApplicationAgentLifetimeGrantSource.Ingress
  record : DurableReceiver.IntentRecord
  ticket : PriorIssue config
  finalRoot : Digest
  admitted : ∃ original : Opened config,
    ∃ accepted : LifetimeGrantIssueAt config original ingress,
      ticket = accepted.prior ∧
      finalRoot = (ApplicationAgentLifetimeGrantAtomicBirth.initializedWrite
        accepted.current.sourceReady).exactPost ∧
      record = DurableReceiver.IntentRecord.ofIntent accepted.intent

/-- The root offered to event26 is the exact post of a write in the admitted
event27 record. This is stronger than decoding a grant from caller bytes. -/
theorem PriorLifetimeGrant.finalRoot_in_record {config : Config}
    (prior : PriorLifetimeGrant config) :
    ∃ write ∈ prior.record.writes, write.exactPost = prior.finalRoot := by
  rcases prior.admitted with ⟨original, accepted, _, rootExact, recordExact⟩
  refine ⟨ApplicationAgentLifetimeGrantAtomicBirth.initializedWrite
    accepted.current.sourceReady, ?_, rootExact.symm⟩
  rw [recordExact]
  exact accepted.current.atomic.initialized_present

theorem LifetimeGrantIssueAt.original_scope {config : Config} {opened : Opened config}
    {ingress : ApplicationAgentLifetimeGrantSource.Ingress}
    (admitted : LifetimeGrantIssueAt config opened ingress) :
    ingress.spec.grant.source.ticketResource = admitted.prior.evidence.spec.ticket.resource ∧
    ingress.spec.grant.participant.app = admitted.prior.evidence.spec.ticket.scope.app ∧
    ingress.spec.grant.participant.session =
      admitted.prior.evidence.spec.ticket.participant.session ∧
    ingress.spec.grant.participant.subject =
      admitted.prior.evidence.spec.ticket.participant.subject ∧
    admitted.prior.evidence.spec.ticket.participant.origin = .agent
      ingress.spec.grant.participant.parentTask
      ingress.spec.grant.participant.originalGeneration ∧
    ingress.spec.grant.approval.ceiling = admitted.prior.evidence.spec.ticket.ceiling :=
  ApplicationAgentLifetimeGrant.matchesIssued_scope _ _ _ _ admitted.scope

/-- Paid agent dispatch joins two prior certificates from this exact replay
walk, then performs fresh app and delegated-payer admission at `opened`.
Original reserve membership and no later purse write cannot be caller flags. -/
structure AgentDispatchAt (config : Config) (opened : Opened config)
    (ingress : ApplicationDispatchAgentIngress.Ingress) where
  private mk ::
  issue : PriorIssue config
  issuePresent : opened.durable.image.accepted[issue.index]? = some issue.evidence.record
  reserve : PriorDispatchReserve config
  reserveIndex : reserve.index = ingress.reserveIndex
  issueBeforeReserve : issue.index < reserve.index
  reservePresent : opened.durable.image.accepted[reserve.index]? = some reserve.raw.record
  untouched : dispatchPurseUntouched
    (opened.durable.image.accepted.drop (reserve.index + 1))
    ingress.reserveContext.purseTask
  bound : ApplicationDispatchAgentReserveCore.ReservedEvidence config
  boundExact : reserve.raw.bindContext ingress.reserveContext = .ok bound
  checked : ApplicationDispatchAgentCore.Checked config opened ingress
    issue.evidence bound

def AgentDispatchAt.intent {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    (admitted : AgentDispatchAt config opened ingress) : DataIntent rootBytes :=
  ApplicationDispatchAgentCore.candidateIntent admitted.checked

/-- Event26 joins only certificates accumulated by the same verified walk:
the event22 ticket, event27 initialized grant, and the original signed v3
purse reserve. Its current dispatch is checked at the present image. -/
structure LifetimeDispatchAt (config : Config) (opened : Opened config)
    (ingress : ApplicationAgentLifetimeDispatchIngress.Ingress) where
  private mk ::
  issue : PriorIssue config
  grant : PriorLifetimeGrant config
  reserve : PriorDispatchReserve config
  ticketExact : issue = grant.ticket
  event22 : issue.evidence.record.event.codecVersion = 22
  issueBeforeGrant : issue.index < grant.index
  grantBeforeReserve : grant.index < reserve.index
  reserveIndex : reserve.index = ingress.reserveIndex
  issuePresent : opened.durable.image.accepted[issue.index]? = some issue.evidence.record
  grantPresent : opened.durable.image.accepted[grant.index]? = some grant.record
  reservePresent : opened.durable.image.accepted[reserve.index]? = some reserve.raw.record
  untouched : dispatchPurseUntouched
    (opened.durable.image.accepted.drop (reserve.index + 1))
    ingress.reserveContext.base.purseTask
  reserved : ApplicationAgentLifetimeDispatchReserveCore.ReservedEvidence config
  reservedExact : ApplicationAgentLifetimeDispatchReserveCore.bindContext
    reserve.raw ingress.reserveContext = .ok reserved
  checked : ApplicationAgentLifetimeDispatchCore.Checked config opened ingress
    issue.evidence.spec issue.evidence.descriptor grant.ingress.spec.grant
    issue.index issue.receipt issue.evidence.ingressBytes grant.index grant.finalRoot reserved

def LifetimeDispatchAt.intent {config : Config} {opened : Opened config}
    {ingress : ApplicationAgentLifetimeDispatchIngress.Ingress}
    (admitted : LifetimeDispatchAt config opened ingress) : DataIntent rootBytes :=
  ApplicationAgentLifetimeDispatchCore.candidateIntent admitted.checked

/-- Evidence is one of the actual privately admitted receiving objects,
not a supplied policy decision, signature Boolean, or arbitrary DataIntent. -/
inductive NativeAdmission (config : Config) (opened : Opened config) : DataIntent rootBytes → Prop
  | birth (accepted : ResourceBirthPolicyController.Concrete.AcceptedBirth
      config.profile config.deployment opened.pins opened.durable
      (logicalHeight config opened.durable)) :
      NativeAdmission config opened (ResourceBirthReceiver.intent accepted)
  | grainBirth {tariff : GrainResourceBirthController.Tariff}
      {source : GrainResourceBirthController.Source}
      {birth : GrainResourceBirthController.PreparedSourceBirth config.profile.compilerProfile
        config.deployment opened.pins opened.durable config.profile.semantics tariff source}
      {grain : GrainResourceBirthTransaction.PreparedTargets config.deployment
        birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
        config.profile.semantics ⟨config.federation, logicalHeight config opened.durable⟩
        (source.grainCommand tariff)}
      {ingress : GrainResourceBirthPolicyController.DecodedIngress}
      (pinned : config.grainBirthTariffValue = .ok tariff)
      (accepted : GrainResourceBirthAdmission.Accepted config.profile config.deployment
        opened.pins opened.durable ⟨config.federation, logicalHeight config opened.durable⟩
        tariff source birth grain ingress) :
      NativeAdmission config opened (GrainResourceBirthReceiver.intent accepted)
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
  | selectiveRelease {ingress : FnSelectiveReleaseIngress.Ingress}
      (accepted : FnSelectiveReleaseAdmission.Accepted config opened ingress) :
      NativeAdmission config opened (accepted.intent config opened ingress)
  | applicationShareIssue {ingress : ApplicationShareIssueSource.Ingress}
      (accepted : ApplicationShareIssueAdmission.Accepted config.profile config
        opened.pins opened.durable (logicalHeight config opened.durable) ingress) :
      NativeAdmission config opened (ApplicationShareIssueReceiver.intent accepted)
  | applicationGrainShareIssue {ingress : ApplicationShareIssueGrainSource.Ingress}
      (accepted : ApplicationShareIssueGrainAdmission.Accepted config.profile config
        opened.pins opened.durable
        ⟨config.federation, logicalHeight config opened.durable⟩ ingress) :
      NativeAdmission config opened (ApplicationShareIssueGrainReceiver.intent accepted)
  | applicationAgentLifetimeGrantIssue
      {ingress : ApplicationAgentLifetimeGrantSource.Ingress}
      (admitted : LifetimeGrantIssueAt config opened ingress) :
      NativeAdmission config opened admitted.intent
  | applicationDispatch {ingress : ApplicationDispatchAdmissionIngress.Ingress}
      (admitted : DispatchAt config opened ingress) :
      NativeAdmission config opened admitted.intent
  | applicationAgentDispatch {ingress : ApplicationDispatchAgentIngress.Ingress}
      (admitted : AgentDispatchAt config opened ingress) :
      NativeAdmission config opened admitted.intent
  | applicationAgentLifetimeDispatch
      {ingress : ApplicationAgentLifetimeDispatchIngress.Ingress}
      (admitted : LifetimeDispatchAt config opened ingress) :
      NativeAdmission config opened admitted.intent
  | selectedSourcePublication {ingress : FnSelectiveReleaseSourcePublication.Ingress}
      (accepted : FnSelectiveReleaseSourceReceiver.Accepted config opened ingress) :
      NativeAdmission config opened (accepted.intent config opened ingress)
  | applicationLifecycleBegin {ingress : ApplicationLifecycleBeginIngress.Ingress}
      (accepted : ApplicationLifecycleBeginReceiver.Accepted config.deployment config.profile
        ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable ingress) :
      NativeAdmission config opened accepted.intent
  | applicationLifecycleClaim {ingress : ApplicationLifecycleClaimIngress.Ingress}
      (admitted : ClaimAt config opened ingress) :
      NativeAdmission config opened admitted.intent
  | applicationLifecycleBeginV2 {ingress : ApplicationLifecycleBeginV2Ingress.Ingress}
      (accepted : ApplicationLifecycleBeginV2Admission.Accepted
        config.deployment config.profile
        ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable ingress) :
      NativeAdmission config opened accepted.intent
  | applicationLifecycleClaimV2 {ingress : ApplicationLifecycleClaimV2Ingress.Ingress}
      (admitted : ClaimAtV2 config opened ingress) :
      NativeAdmission config opened admitted.intent
  | applicationLifecycleCompletion {ingress : ApplicationLifecycleCompletionIngress.Ingress}
      (admitted : CompletionAt config opened ingress) :
      NativeAdmission config opened admitted.intent
  | applicationLifecycleBeginV3 {ingress : ApplicationLifecycleBeginV3Ingress.Ingress}
      (admitted : BeginAtV3 config opened ingress) :
      NativeAdmission config opened admitted.intent
  | applicationLifecycleClaimV3 {ingress : ApplicationLifecycleClaimV3Ingress.Ingress}
      (admitted : ClaimAtV3 config opened ingress) :
      NativeAdmission config opened admitted.intent
  | applicationLifecycleCompletionV2
      {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
      (admitted : CompletionAtV2 config opened ingress) :
      NativeAdmission config opened admitted.intent
  | fnConsumerNamespace {ingress : FnConsumerNamespaceRegistration.Ingress}
      {legacy : Option FnConsumerNamespaceAdmissionAt.Legacy}
      (accepted : FnConsumerNamespaceAdmissionAt.Conditional config opened legacy ingress) :
      NativeAdmission config opened (accepted.intent config opened legacy ingress)
  | fnSelectedPoll {ingress : FnSelectedPollCoverage.Ingress}
      {cursor : FnConsumerFrontierCore.Cursor}
      {original : FnSelectedPollReleaseShape.Original}
      {registration : FnConsumerNamespaceHistory.Original}
      (accepted : FnSelectedPollAdmissionAt.Accepted config opened cursor original
        registration ingress) :
      NativeAdmission config opened
        (accepted.intent config opened cursor original registration ingress)
  | fnEmptyPollV2 {ingress : FnEmptyPollProgressV2.Ingress}
      {cursor : FnConsumerFrontierCore.Cursor}
      {registration : FnConsumerNamespaceHistory.Original}
      (accepted : FnEmptyPollAdmissionAtV2.Accepted config opened cursor registration ingress) :
      NativeAdmission config opened
        (accepted.intent config opened cursor registration ingress)

structure OrdinaryAt (config : Config) (opened : Opened config)
    (intent : DataIntent rootBytes) where
  command : DeclaredResourceController.Command
  signed : DeclaredResourceController.SignedCommand
  prepared : DeclaredResourceController.PreparedInvocation config.deployment
    config.profile ⟨config.federation, logicalHeight config opened.durable⟩
    opened.durable command
  shape : DeclaredResourceController.PhysicalShape prepared
  accepted : DeclaredResourceController.AcceptedInvocation prepared signed
  intentExact : intent = accepted.dataIntent shape

inductive IssueAdmission (config : Config) (opened : Opened config)
    (intent : DataIntent rootBytes) : Type where
  | legacy (ingress : ApplicationShareIssueSource.Ingress)
      (accepted : ApplicationShareIssueAdmission.Accepted config.profile config opened.pins
        opened.durable (logicalHeight config opened.durable) ingress)
      (intentExact : intent = ApplicationShareIssueReceiver.intent accepted)
  | grain (ingress : ApplicationShareIssueGrainSource.Ingress)
      (accepted : ApplicationShareIssueGrainAdmission.Accepted config.profile config opened.pins
        opened.durable ⟨config.federation, logicalHeight config opened.durable⟩ ingress)
      (intentExact : intent = ApplicationShareIssueGrainReceiver.intent accepted)

structure Derived (config : Config) (opened : Opened config) where
  private mk ::
  intent : DataIntent rootBytes
  admission : NativeAdmission config opened intent
  issue : Option (IssueAdmission config opened intent)
  begin : Option (Σ ingress : ApplicationLifecycleBeginIngress.Ingress,
    { accepted : ApplicationLifecycleBeginReceiver.Accepted config.deployment config.profile
        ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable ingress //
      intent = accepted.intent })
  beginV2 : Option (Σ ingress : ApplicationLifecycleBeginV2Ingress.Ingress,
    { accepted : ApplicationLifecycleBeginV2Admission.Accepted
        config.deployment config.profile
        ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable ingress //
      intent = accepted.intent })
  claimV2 : Option (Σ ingress : ApplicationLifecycleClaimV2Ingress.Ingress,
    { admitted : ClaimAtV2 config opened ingress // intent = admitted.intent })
  ordinary : Option (OrdinaryAt config opened intent) := none
  beginV3 : Option (Σ ingress : ApplicationLifecycleBeginV3Ingress.Ingress,
    { admitted : BeginAtV3 config opened ingress // intent = admitted.intent }) := none
  claimV3 : Option (Σ ingress : ApplicationLifecycleClaimV3Ingress.Ingress,
    { admitted : ClaimAtV3 config opened ingress // intent = admitted.intent }) := none
  completionV2 : Option (Σ ingress : ApplicationLifecycleCompletionV2Ingress.Ingress,
    { admitted : CompletionAtV2 config opened ingress // intent = admitted.intent }) := none
  grantIssue : Option (Σ ingress : ApplicationAgentLifetimeGrantSource.Ingress,
    { admitted : LifetimeGrantIssueAt config opened ingress // intent = admitted.intent }) := none

/-- Retain the exact admitted ordinary invocation for the persistent native
readback path. The constructor accepts the typed current-image admission, not
caller-supplied intent bytes. -/
def Derived.ofInvoke {config : Config} {opened : Opened config}
    {command : DeclaredResourceController.Command}
    (prepared : DeclaredResourceController.PreparedInvocation config.deployment
      config.profile ⟨config.federation, logicalHeight config opened.durable⟩
      opened.durable command)
    (signed : DeclaredResourceController.SignedCommand)
    (shape : DeclaredResourceController.PhysicalShape prepared)
    (accepted : DeclaredResourceController.AcceptedInvocation prepared signed) :
    Derived config opened :=
  ⟨accepted.dataIntent shape, .invoke prepared signed shape accepted,
    none, none, none, none, some ⟨_, signed, prepared, shape, accepted, rfl⟩,
    none, none, none, none⟩

/-- Reuse the very same typed dispatch admission for the exact CAS readback
fast path. No second signature check or caller-created Derived is needed. -/
def DispatchAt.toDerived {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : DispatchAt config opened ingress) : Derived config opened :=
  ⟨admitted.intent, .applicationDispatch admitted, none, none, none, none, none,
    none, none, none, none⟩

def AgentDispatchAt.toDerived {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    (admitted : AgentDispatchAt config opened ingress) : Derived config opened :=
  ⟨admitted.intent, .applicationAgentDispatch admitted, none, none, none, none, none,
    none, none, none, none⟩

def LifetimeDispatchAt.toDerived {config : Config} {opened : Opened config}
    {ingress : ApplicationAgentLifetimeDispatchIngress.Ingress}
    (admitted : LifetimeDispatchAt config opened ingress) : Derived config opened :=
  ⟨admitted.intent, .applicationAgentLifetimeDispatch admitted, none, none, none,
    none, none, none, none, none, none⟩

theorem LifetimeDispatchAt.toDerived_intent {config : Config} {opened : Opened config}
    {ingress : ApplicationAgentLifetimeDispatchIngress.Ingress}
    (admitted : LifetimeDispatchAt config opened ingress) :
    admitted.toDerived.intent = admitted.intent := rfl

theorem AgentDispatchAt.toDerived_intent {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAgentIngress.Ingress}
    (admitted : AgentDispatchAt config opened ingress) :
    admitted.toDerived.intent = admitted.intent := rfl

def ClaimAt.toDerived {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleClaimIngress.Ingress}
    (admitted : ClaimAt config opened ingress) : Derived config opened :=
  ⟨admitted.intent, .applicationLifecycleClaim admitted, none, none, none, none, none,
    none, none, none, none⟩

def ClaimAtV2.toDerived {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleClaimV2Ingress.Ingress}
    (admitted : ClaimAtV2 config opened ingress) : Derived config opened :=
  ⟨admitted.intent, .applicationLifecycleClaimV2 admitted,
    none, none, none, some ⟨ingress, ⟨admitted, rfl⟩⟩, none,
    none, none, none, none⟩

def CompletionAt.toDerived {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (admitted : CompletionAt config opened ingress) : Derived config opened :=
  ⟨admitted.intent, .applicationLifecycleCompletion admitted,
    none, none, none, none, none, none, none, none, none⟩

def ClaimAtV3.toDerived {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleClaimV3Ingress.Ingress}
    (admitted : ClaimAtV3 config opened ingress) : Derived config opened :=
  ⟨admitted.intent, .applicationLifecycleClaimV3 admitted,
    none, none, none, none, none, none,
    some ⟨ingress, ⟨admitted, rfl⟩⟩, none, none⟩

theorem ClaimAtV3.toDerived_intent {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleClaimV3Ingress.Ingress}
    (admitted : ClaimAtV3 config opened ingress) :
    admitted.toDerived.intent = admitted.intent := rfl

def CompletionAtV2.toDerived {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
    (admitted : CompletionAtV2 config opened ingress) : Derived config opened :=
  ⟨admitted.intent, .applicationLifecycleCompletionV2 admitted,
    none, none, none, none, none, none, none,
    some ⟨ingress, ⟨admitted, rfl⟩⟩, none⟩

theorem CompletionAtV2.toDerived_intent {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
    (admitted : CompletionAtV2 config opened ingress) :
    admitted.toDerived.intent = admitted.intent := rfl

theorem CompletionAt.toDerived_intent {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (admitted : CompletionAt config opened ingress) :
    admitted.toDerived.intent = admitted.intent := rfl

theorem ClaimAtV2.toDerived_intent {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleClaimV2Ingress.Ingress}
    (admitted : ClaimAtV2 config opened ingress) :
    admitted.toDerived.intent = admitted.intent := rfl

theorem ClaimAt.toDerived_intent {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleClaimIngress.Ingress}
    (admitted : ClaimAt config opened ingress) :
    admitted.toDerived.intent = admitted.intent := rfl

theorem DispatchAt.toDerived_intent {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : DispatchAt config opened ingress) :
    admitted.toDerived.intent = admitted.intent := rfl

/-- This lookup is only over issue certificates minted by earlier steps in the
same replay walk. Matching ingress bytes do not themselves confer authority. -/
private def priorIssueFor (config : Config)
    (issues : List (PriorIssue config))
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) :
    Option (PriorIssue config) :=
  issues.find? (fun issue =>
    decide (ingress.issueIngressBytes =
      issue.evidence.ingressBytes))

/-- Select only the event22 source whose verified original index and complete
receipt are named by the grant. A structurally similar legacy event15 ticket
cannot issue a lifetime route. -/
private def priorIssueForLifetimeGrant (config : Config)
    (issues : List (PriorIssue config))
    (ingress : ApplicationAgentLifetimeGrantSource.Ingress) :
    Option (PriorIssue config) :=
  issues.find? fun issue => decide
    (issue.index = ingress.spec.grant.source.issueIndex ∧
      issue.receipt = ingress.spec.grant.source.issueReceipt ∧
      issue.evidence.record.event.codecVersion = 22)

private def priorBeginFor (config : Config) (begins : List (PriorBegin config))
    (ingress : ApplicationLifecycleClaimIngress.Ingress) :
    Option (PriorBegin config) :=
  begins.find? (fun prior => decide
    (prior.index = ingress.source.originalIndex ∧
      prior.ingress = ingress.source.begin))

private def priorBeginV2For (config : Config)
    (begins : List (PriorBeginV2 config))
    (ingress : ApplicationLifecycleClaimV2Ingress.Ingress) :
    Option (PriorBeginV2 config) :=
  begins.find? (fun prior => decide
    (prior.index = ingress.base.source.originalIndex ∧
      prior.ingress = ingress.originalBegin))

private def priorBeginV3For (config : Config)
    (begins : List (PriorBeginV3 config))
    (ingress : ApplicationLifecycleClaimV3Ingress.Ingress) :
    Option (PriorBeginV3 config) :=
  begins.find? (fun prior => decide
    (prior.index = ingress.base.source.originalIndex ∧
      prior.ingress = ingress.originalBegin))

private theorem priorBeginV2For_empty (config : Config)
    (ingress : ApplicationLifecycleClaimV2Ingress.Ingress) :
    priorBeginV2For config [] ingress = none := rfl

/-- A dispatch before any admitted issue has no historical source to select. -/
private theorem priorIssueFor_empty (config : Config)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) :
    priorIssueFor config [] ingress = none := rfl

private theorem priorBeginFor_empty (config : Config)
    (ingress : ApplicationLifecycleClaimIngress.Ingress) :
    priorBeginFor config [] ingress = none := rfl

private def admitLifetimeGrantIssueAt (config : Config) (opened : Opened config)
    (issues : List (PriorIssue config))
    (ingress : ApplicationAgentLifetimeGrantSource.Ingress) :
    IO (Except String (LifetimeGrantIssueAt config opened ingress)) := do
  let some prior := priorIssueForLifetimeGrant config issues ingress
    | return .error "agent lifetime grant original event22 issue absent"
  if originalEvent22 : prior.evidence.record.event.codecVersion = 22 then
    if originalIndex : prior.index = ingress.spec.grant.source.issueIndex then
      if originalReceipt : prior.receipt = ingress.spec.grant.source.issueReceipt then
        if scope : ingress.spec.grant.matchesIssued prior.evidence.spec
            prior.index prior.receipt = true then
          if recordBytes : (opened.durable.image.accepted[prior.index]?.map
              DurableReceiverCodec.intentStream.encode) =
              some (DurableReceiverCodec.intentStream.encode prior.evidence.record) then
            have present : opened.durable.image.accepted[prior.index]? =
                some prior.evidence.record := by
              cases found : opened.durable.image.accepted[prior.index]? with
              | none => simp [found] at recordBytes
              | some record =>
                simp only [found, Option.map_some, Option.some.injEq] at recordBytes
                have exact := (lawful_encode_injective
                  DurableReceiverCodec.intentStream.toLawful) recordBytes
                simpa only [found, Option.some.injEq] using exact
            match ← ApplicationAgentLifetimeGrantAdmission.admitNative config.profile
                config opened.pins config.signature opened.durable
                (logicalHeight config opened.durable) ingress.canonicalBytes with
            | .error _ => return .error "agent lifetime grant native admission refused"
            | .ok ⟨decoded, accepted⟩ =>
              if same : decoded = ingress then
                have current : ApplicationAgentLifetimeGrantAdmission.Accepted config.profile
                    config opened.pins opened.durable
                    (logicalHeight config opened.durable) ingress := by
                  cases same
                  exact accepted
                return .ok ⟨prior, originalEvent22, originalIndex,
                  originalReceipt, present, scope, current⟩
              else return .error "agent lifetime grant ingress changed at native admission"
          else return .error "agent lifetime grant original record differs"
        else return .error "agent lifetime grant exceeds original ticket scope"
      else return .error "agent lifetime grant original receipt differs"
    else return .error "agent lifetime grant original issue index differs"
  else return .error "agent lifetime grant original ticket was not event22"

private def admitDispatchAt (config : Config) (opened : Opened config)
    (issues : List (PriorIssue config))
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) :
    IO (Except String (DispatchAt config opened ingress)) := do
  let some prior := priorIssueFor config issues ingress
    | return .error "historical dispatch issue absent from admitted prefix"
  match found : opened.durable.image.accepted[prior.index]? with
  | none => return .error "historical dispatch issue record absent from prefix"
  | some original =>
    if exactBytes : DurableReceiverCodec.intentStream.encode original =
        DurableReceiverCodec.intentStream.encode prior.evidence.record then
      have originalExact : original = prior.evidence.record :=
        (lawful_encode_injective DurableReceiverCodec.intentStream.toLawful) exactBytes
      have present : opened.durable.image.accepted[prior.index]? =
          some prior.evidence.record := by
        simpa only [originalExact] using found
      match ← ApplicationDispatchHistoricalCore.checkCurrent config opened.durable
          ingress prior.evidence with
      | .error _ => return .error "historical dispatch current admission refused"
      | .ok checked => return .ok ⟨prior, present, checked⟩
    else return .error "historical dispatch issue record differs from prefix"

/-- Both certificates were minted by this same admitted walk. The full
verified suffix, not merely the current purse value, must leave the original
reserve untouched. -/
private def admitAgentDispatchAt (config : Config) (opened : Opened config)
    (issues : List (PriorIssue config))
    (reserves : List (PriorDispatchReserve config))
    (ingress : ApplicationDispatchAgentIngress.Ingress) :
    IO (Except String (AgentDispatchAt config opened ingress)) := do
  let some issue := priorIssueFor config issues ingress.dispatch
    | return .error "agent dispatch issued ticket absent from admitted prefix"
  let some reserve := reserves.find? (fun prior => prior.index == ingress.reserveIndex)
    | return .error "agent dispatch reserve absent from admitted prefix"
  if reserveIndex : reserve.index = ingress.reserveIndex then
    if issueBeforeReserve : issue.index < reserve.index then
      if issueBytes : (opened.durable.image.accepted[issue.index]?.map
          DurableReceiverCodec.intentStream.encode) =
        some (DurableReceiverCodec.intentStream.encode issue.evidence.record) then
        have issuePresent : opened.durable.image.accepted[issue.index]? =
            some issue.evidence.record := by
          cases found : opened.durable.image.accepted[issue.index]? with
          | none => simp [found] at issueBytes
          | some record =>
            simp only [found, Option.map_some, Option.some.injEq] at issueBytes
            have exact := (lawful_encode_injective
              DurableReceiverCodec.intentStream.toLawful) issueBytes
            simpa only [found, Option.some.injEq] using exact
        if reserveBytes : (opened.durable.image.accepted[reserve.index]?.map
            DurableReceiverCodec.intentStream.encode) =
            some (DurableReceiverCodec.intentStream.encode reserve.raw.record) then
          have reservePresent : opened.durable.image.accepted[reserve.index]? =
              some reserve.raw.record := by
            cases found : opened.durable.image.accepted[reserve.index]? with
            | none => simp [found] at reserveBytes
            | some record =>
              simp only [found, Option.map_some, Option.some.injEq] at reserveBytes
              have exact := (lawful_encode_injective
                DurableReceiverCodec.intentStream.toLawful) reserveBytes
              simpa only [found, Option.some.injEq] using exact
          if untouched : dispatchPurseUntouched
              (opened.durable.image.accepted.drop (reserve.index + 1))
              ingress.reserveContext.purseTask then
            match boundExact : reserve.raw.bindContext ingress.reserveContext with
            | .error detail => return .error detail
            | .ok bound =>
              match ← ApplicationDispatchAgentCore.checkCurrent config opened ingress
                  issue.evidence bound with
              | .error detail => return .error detail
              | .ok checked =>
                return .ok ⟨issue, issuePresent, reserve, reserveIndex, issueBeforeReserve,
                  reservePresent, untouched, bound, boundExact, checked⟩
          else return .error "agent dispatch purse changed after original reserve"
        else return .error "agent dispatch original reserve record differs"
      else return .error "agent dispatch original issue record differs"
    else return .error "agent dispatch reserve predates issued ticket"
  else return .error "agent dispatch reserve index differs"

private def admitLifetimeDispatchAt (config : Config) (opened : Opened config)
    (grants : List (PriorLifetimeGrant config))
    (reserves : List (PriorDispatchReserve config))
    (ingress : ApplicationAgentLifetimeDispatchIngress.Ingress) :
    IO (Except String (LifetimeDispatchAt config opened ingress)) := do
  let some grant := grants.find? (fun prior => decide
      (prior.index = ingress.reserveContext.grantIssueIndex ∧
        prior.ticket.evidence.ingressBytes = ingress.dispatch.issueIngressBytes))
    | return .error "lifetime dispatch certified grant absent from admitted prefix"
  let issue := grant.ticket
  let some reserve := reserves.find? (fun prior => prior.index == ingress.reserveIndex)
    | return .error "lifetime dispatch signed reserve absent from admitted prefix"
  if event22 : issue.evidence.record.event.codecVersion = 22 then
    if issueBeforeGrant : issue.index < grant.index then
      if grantBeforeReserve : grant.index < reserve.index then
        if reserveIndex : reserve.index = ingress.reserveIndex then
          if issueBytes : (opened.durable.image.accepted[issue.index]?.map
              DurableReceiverCodec.intentStream.encode) =
              some (DurableReceiverCodec.intentStream.encode issue.evidence.record) then
            have issuePresent : opened.durable.image.accepted[issue.index]? =
                some issue.evidence.record := by
              cases found : opened.durable.image.accepted[issue.index]? with
              | none => simp [found] at issueBytes
              | some record =>
                simp only [found, Option.map_some, Option.some.injEq] at issueBytes
                have exact := (lawful_encode_injective
                  DurableReceiverCodec.intentStream.toLawful) issueBytes
                simpa only [found, Option.some.injEq] using exact
            if grantBytes : (opened.durable.image.accepted[grant.index]?.map
                DurableReceiverCodec.intentStream.encode) =
                some (DurableReceiverCodec.intentStream.encode grant.record) then
              have grantPresent : opened.durable.image.accepted[grant.index]? =
                  some grant.record := by
                cases found : opened.durable.image.accepted[grant.index]? with
                | none => simp [found] at grantBytes
                | some record =>
                  simp only [found, Option.map_some, Option.some.injEq] at grantBytes
                  have exact := (lawful_encode_injective
                    DurableReceiverCodec.intentStream.toLawful) grantBytes
                  simpa only [found, Option.some.injEq] using exact
              if reserveBytes : (opened.durable.image.accepted[reserve.index]?.map
                  DurableReceiverCodec.intentStream.encode) =
                  some (DurableReceiverCodec.intentStream.encode reserve.raw.record) then
                have reservePresent : opened.durable.image.accepted[reserve.index]? =
                    some reserve.raw.record := by
                  cases found : opened.durable.image.accepted[reserve.index]? with
                  | none => simp [found] at reserveBytes
                  | some record =>
                    simp only [found, Option.map_some, Option.some.injEq] at reserveBytes
                    have exact := (lawful_encode_injective
                      DurableReceiverCodec.intentStream.toLawful) reserveBytes
                    simpa only [found, Option.some.injEq] using exact
                if untouched : dispatchPurseUntouched
                    (opened.durable.image.accepted.drop (reserve.index + 1))
                    ingress.reserveContext.base.purseTask then
                  match reservedExact : ApplicationAgentLifetimeDispatchReserveCore.bindContext
                      reserve.raw ingress.reserveContext with
                  | .error detail => return .error detail
                  | .ok reserved =>
                    match ← ApplicationAgentLifetimeDispatchCore.checkCurrent config opened
                        ingress issue.evidence.spec issue.evidence.descriptor
                        grant.ingress.spec.grant issue.index issue.receipt
                        issue.evidence.ingressBytes grant.index grant.finalRoot reserved with
                    | .error detail => return .error detail
                    | .ok checked =>
                      return .ok ⟨issue, grant, reserve, rfl, event22, issueBeforeGrant,
                        grantBeforeReserve, reserveIndex, issuePresent, grantPresent,
                        reservePresent, untouched, reserved, reservedExact, checked⟩
                else return .error "lifetime dispatch purse changed after reserve"
              else return .error "lifetime dispatch original reserve record differs"
            else return .error "lifetime dispatch original grant record differs"
          else return .error "lifetime dispatch original ticket record differs"
        else return .error "lifetime dispatch reserve index differs"
      else return .error "lifetime dispatch reserve predates certified grant"
    else return .error "lifetime dispatch grant predates original ticket"
  else return .error "lifetime dispatch ticket was not event22"

private def admitClaimAt (config : Config) (opened : Opened config)
    (begins : List (PriorBegin config))
    (ingress : ApplicationLifecycleClaimIngress.Ingress) :
    IO (Except String (ClaimAt config opened ingress)) := do
  let some prior := priorBeginFor config begins ingress
    | return .error "historical lifecycle begin absent from admitted prefix"
  if indexExact : prior.index = ingress.source.originalIndex then
    if ingressExact : prior.ingress = ingress.source.begin then
      match found : opened.durable.image.accepted[prior.index]? with
      | none => return .error "historical lifecycle begin record absent from prefix"
      | some record =>
        if physicalExact : DurableReceiverCodec.intentStream.encode record =
            DurableReceiverCodec.intentStream.encode prior.record then
          have exact : record = prior.record :=
            (lawful_encode_injective DurableReceiverCodec.intentStream.toLawful)
              physicalExact
          have present : opened.durable.image.accepted[prior.index]? =
              some prior.record := by simpa only [exact] using found
          match ← ApplicationLifecycleClaimCore.prepare config opened ingress with
          | .error _ => return .error "historical lifecycle claim current admission refused"
          | .ok conditional =>
            if recordExact : DurableReceiverCodec.intentStream.encode prior.record =
                DurableReceiverCodec.intentStream.encode
                  (DurableReceiver.IntentRecord.ofIntent
                    conditional.original.admitted.intent) then
              have sourceExact : prior.record =
                  DurableReceiver.IntentRecord.ofIntent
                    conditional.original.admitted.intent :=
                (lawful_encode_injective DurableReceiverCodec.intentStream.toLawful)
                  recordExact
              return .ok ⟨prior, indexExact, ingressExact, present,
                conditional, sourceExact⟩
            else return .error "historical lifecycle begin differs from source-admitted intent"
        else return .error "historical lifecycle begin record differs from prefix"
    else return .error "historical lifecycle begin ingress differs"
  else return .error "historical lifecycle begin index differs"

private def admitClaimV2At (config : Config) (opened : Opened config)
    (begins : List (PriorBeginV2 config))
    (ingress : ApplicationLifecycleClaimV2Ingress.Ingress) :
    IO (Except String (ClaimAtV2 config opened ingress)) := do
  let some prior := priorBeginV2For config begins ingress
    | return .error "descriptor-bound lifecycle begin absent from admitted prefix"
  if indexExact : prior.index = ingress.base.source.originalIndex then
    if ingressExact : prior.ingress = ingress.originalBegin then
      match found : opened.durable.image.accepted[prior.index]? with
      | none => return .error "descriptor-bound lifecycle begin record absent"
      | some record =>
        if physicalExact : DurableReceiverCodec.intentStream.encode record =
            DurableReceiverCodec.intentStream.encode prior.record then
          have exact : record = prior.record :=
            (lawful_encode_injective DurableReceiverCodec.intentStream.toLawful)
              physicalExact
          have present : opened.durable.image.accepted[prior.index]? =
              some prior.record := by simpa only [exact] using found
          match ← ApplicationLifecycleClaimV2Core.prepare config opened ingress with
          | .error _ => return .error "descriptor-bound lifecycle claim current admission refused"
          | .ok conditional =>
            if sourceBytes : DurableReceiverCodec.intentStream.encode prior.record =
                DurableReceiverCodec.intentStream.encode
                  (DurableReceiver.IntentRecord.ofIntent
                    conditional.originalAccepted.intent) then
              have recordExact : prior.record =
                  DurableReceiver.IntentRecord.ofIntent
                    conditional.originalAccepted.intent :=
                (lawful_encode_injective DurableReceiverCodec.intentStream.toLawful)
                  sourceBytes
              return .ok ⟨prior, indexExact, ingressExact, present,
                conditional, recordExact⟩
            else return .error "descriptor-bound lifecycle begin differs from original intent"
        else return .error "descriptor-bound lifecycle begin record differs"
    else return .error "descriptor-bound lifecycle begin ingress differs"
  else return .error "descriptor-bound lifecycle begin index differs"

/-- Event24 can select only an event23 BEGIN admitted earlier by this same
verified walk; the structural original-prefix recheck is additional evidence. -/
private def admitClaimV3At (config : Config) (opened : Opened config)
    (begins : List (PriorBeginV3 config))
    (ingress : ApplicationLifecycleClaimV3Ingress.Ingress) :
    IO (Except String (ClaimAtV3 config opened ingress)) := do
  let some prior := priorBeginV3For config begins ingress
    | return .error "launch-bound BEGIN absent from admitted prefix"
  if indexExact : prior.index = ingress.base.source.originalIndex then
    if ingressExact : prior.ingress = ingress.originalBegin then
      match found : opened.durable.image.accepted[prior.index]? with
      | none => return .error "launch-bound BEGIN record absent"
      | some record =>
        if physicalExact : DurableReceiverCodec.intentStream.encode record =
            DurableReceiverCodec.intentStream.encode prior.record then
          have exact : record = prior.record :=
            (lawful_encode_injective DurableReceiverCodec.intentStream.toLawful)
              physicalExact
          have present : opened.durable.image.accepted[prior.index]? =
              some prior.record := by simpa only [exact] using found
          match ← ApplicationLifecycleClaimV3Core.prepare config opened ingress with
          | .error detail => return .error detail
          | .ok conditional =>
            if sourceBytes : DurableReceiverCodec.intentStream.encode prior.record =
                DurableReceiverCodec.intentStream.encode
                  (DurableReceiver.IntentRecord.ofIntent
                    conditional.originalAccepted.intent) then
              have recordExact : prior.record =
                  DurableReceiver.IntentRecord.ofIntent
                    conditional.originalAccepted.intent :=
                (lawful_encode_injective DurableReceiverCodec.intentStream.toLawful)
                  sourceBytes
              return .ok ⟨prior, indexExact, ingressExact, present,
                conditional, recordExact⟩
            else return .error "launch-bound BEGIN differs from original intent"
        else return .error "launch-bound BEGIN record differs from prefix"
    else return .error "launch-bound BEGIN ingress differs"
  else return .error "launch-bound BEGIN index differs"

/-- The lower completion preparation re-admits a structural prefix; this
join additionally requires that exact claim to occur in the private history
accumulated only after the replay walk's successful native step. -/
private def admitCompletionAt (config : Config) (opened : Opened config)
    (claimsV2 : List (PriorClaimV2 config))
    (ingress : ApplicationLifecycleCompletionIngress.Ingress) :
    IO (Except String (CompletionAt config opened ingress)) := do
  let conditional ← match ← ApplicationLifecycleCompletionAdmission.prepareConditional
      config opened ingress with
    | .error detail => return .error detail
    | .ok candidate => pure candidate
  let some prior := claimsV2.find? (fun prior => prior.index == conditional.historical.index)
    | return .error "completion original claim absent from admitted history"
  if indexExact : prior.index = conditional.historical.index then
    if ingressExact : prior.ingress = ingress.source.originalClaim then
      if recordBytes : DurableReceiverCodec.intentStream.encode prior.record =
          DurableReceiverCodec.intentStream.encode conditional.historical.selected.record then
        have recordExact : prior.record = conditional.historical.selected.record :=
          (lawful_encode_injective DurableReceiverCodec.intentStream.toLawful) recordBytes
        have present : opened.durable.image.accepted[prior.index]? =
            some prior.record := by
          rw [indexExact, recordExact]
          exact conditional.historical.selected.atIndex
        return .ok ⟨prior, conditional, indexExact, ingressExact, recordExact, present⟩
      else return .error "completion original claim record differs from admitted history"
    else return .error "completion original claim ingress differs from admitted history"
  else return .error "completion original claim index differs from admitted history"

private def admitCompletionV2At (config : Config) (opened : Opened config)
    (claims : List (PriorClaimV3 config))
    (running : List (PriorRunningV3 config))
    (ingress : ApplicationLifecycleCompletionV2Ingress.Ingress) :
    IO (Except String (CompletionAtV2 config opened ingress)) := do
  let conditional ← match ← ApplicationLifecycleCompletionV2Admission.prepareConditional
      config opened ingress with
    | .error detail => return .error detail
    | .ok candidate => pure candidate
  let some prior := claims.find? (fun prior => prior.index == conditional.historical.index)
    | return .error "v2 completion original v3 claim absent from admitted history"
  if indexExact : prior.index = conditional.historical.index then
    if ingressExact : prior.ingress = ingress.source.originalClaim then
      if recordBytes : DurableReceiverCodec.intentStream.encode prior.record =
          DurableReceiverCodec.intentStream.encode conditional.historical.selected.record then
        have recordExact : prior.record = conditional.historical.selected.record :=
          (lawful_encode_injective DurableReceiverCodec.intentStream.toLawful) recordBytes
        have present : opened.durable.image.accepted[prior.index]? =
            some prior.record := by
          rw [indexExact, recordExact]
          exact conditional.historical.selected.atIndex
        let runningCheck : CompletionV2Running config opened ingress ←
          if kind : ingress.source.originalBegin.base.source.kind = .stop then
            match selectRunningAt opened running
                ingress.source.originalBegin.base.source with
            | .error detail => return .error detail
            | .ok exact =>
                if unitExact : ingress.source.physical.report.unit =
                    exact.prior.ingress.source.physical.report.unit then
                  if invocationExact : ingress.source.physical.report.invocationId =
                      exact.prior.ingress.source.physical.report.invocationId then
                    if controlGroupExact : ingress.source.physical.report.controlGroup =
                        exact.prior.ingress.source.physical.report.controlGroup then
                      if custodyExact : ingress.source.physical.report.volumeCustody =
                          exact.prior.ingress.source.physical.report.volumeCustody then
                        pure (.stop exact unitExact invocationExact controlGroupExact
                          custodyExact)
                      else return .error "STOP volume custody differs from running incarnation"
                    else return .error "STOP cgroup differs from admitted running incarnation"
                  else return .error "STOP invocation differs from admitted running incarnation"
                else return .error "STOP unit differs from admitted running incarnation"
          else pure (.other kind)
        return .ok ⟨prior, conditional, indexExact, ingressExact, recordExact,
          present, runningCheck⟩
      else return .error "v2 completion original claim record differs"
    else return .error "v2 completion original claim ingress differs"
  else return .error "v2 completion original claim index differs"

/-- Fresh native admission is mandatory even if the final image contains an
identical receipt. The issue context is private to the chronological replay
walk; no caller-provided signed issue bytes can populate it. -/
private def derive (config : Config) (opened : Opened config)
    (issues : List (PriorIssue config))
    (reserves : List (PriorDispatchReserve config))
    (begins : List (PriorBegin config))
    (beginsV2 : List (PriorBeginV2 config))
    (claimsV2 : List (PriorClaimV2 config))
    (beginsV3 : List (PriorBeginV3 config))
    (claimsV3 : List (PriorClaimV3 config))
    (createdV3 : List (PriorCreatedV3 config))
    (runningV3 : List (PriorRunningV3 config))
    (grants : List (PriorLifetimeGrant config))
    (frontier : FnConsumerFrontierReplay.Audit)
    (releases : List PriorSelectedRelease)
    (bytes : List UInt8) :
    IO (Except String (Derived config opened)) := do
  let height := logicalHeight config opened.durable
  if let some ingress := CapabilityRevocationReceiver.decodeIngress bytes then
    match ← CapabilityRevocationReceiver.admitDecodedNative config.deployment config.profile
        ⟨config.federation, height⟩ opened.durable config.signature ingress with
    | .error reason => return .error s!"revocation refused: {repr reason}"
    | .ok accepted => return .ok ⟨CapabilityRevocationReceiver.intent accepted, .revoke accepted, none, none, none, none, none, none, none, none, none⟩
  if let some ingress := FnSelectiveReleaseIngress.ingressCodec.decode bytes then
    match ← FnSelectiveReleaseAdmission.admit config opened ingress with
    | .error _ => return .error "historical selected release admission refused"
    | .ok accepted =>
        return .ok ⟨accepted.intent config opened ingress, .selectiveRelease accepted, none, none, none, none, none, none, none, none, none⟩
  if let some ingress := FnConsumerNamespaceRegistration.ingressCodec.decode bytes then
    unless frontier.registrationAbsent ingress.spec.consumerNamespace do
      return .error "fn consumer namespace already registered"
    let .ok legacy := frontier.legacyFor ingress.spec
      | return .error "fn consumer namespace legacy anchor differs"
    match ← FnConsumerNamespaceAdmissionAt.prepareConditional config opened legacy ingress with
    | .error detail => return .error detail
    | .ok accepted =>
        return .ok ⟨accepted.intent config opened legacy ingress,
          .fnConsumerNamespace accepted, none, none, none, none, none, none, none, none, none⟩
  if let some ingress := FnSelectedPollCoverage.ingressCodec.decode bytes then
    let .ok cursor := frontier.cursor ingress.spec.evidence.key
      | return .error "historical selected fn frontier is ambiguous"
    let .ok registration := frontier.registrationFor ingress.spec.evidence.key
        ingress.spec.registrationReceipt
      | return .error "historical selected fn registration differs"
    let some original := selectedReleaseFor config opened releases
        ingress.spec.evidence.releaseKey
      | return .error "historical selected fn release is absent"
    match ← FnSelectedPollAdmissionAt.admitAt config opened cursor original registration ingress with
    | .error detail => return .error detail
    | .ok accepted =>
        return .ok ⟨accepted.intent config opened cursor original registration ingress,
          .fnSelectedPoll accepted, none, none, none, none, none, none, none, none, none⟩
  if let some ingress := FnEmptyPollProgressV2.ingressCodec.decode bytes then
    let .ok cursor := frontier.cursor ingress.spec.evidence.key
      | return .error "historical empty fn frontier is ambiguous"
    let .ok registration := frontier.registrationFor ingress.spec.evidence.key
        ingress.spec.registrationReceipt
      | return .error "historical empty fn registration differs"
    match ← FnEmptyPollAdmissionAtV2.admitAt config opened cursor registration ingress with
    | .error detail => return .error detail
    | .ok accepted =>
        return .ok ⟨accepted.intent config opened cursor registration ingress,
          .fnEmptyPollV2 accepted, none, none, none, none, none, none, none, none, none⟩
  if (ApplicationShareIssueSource.ingressCodec.decode bytes).isSome then
    match ← ApplicationShareIssueAdmission.admitNative config.profile config opened.pins
        config.signature opened.durable height bytes with
    | .error _ => return .error "historical application share issue admission refused"
    | .ok ⟨issueIngress, accepted⟩ =>
        return .ok ⟨ApplicationShareIssueReceiver.intent accepted,
          .applicationShareIssue accepted, some (.legacy issueIngress accepted rfl),
          none, none, none, none, none, none, none, none⟩
  if (ApplicationShareIssueGrainSource.codec.decode bytes).isSome then
    let ambient : DeclaredResourceController.Ambient := ⟨config.federation, height⟩
    match ← ApplicationShareIssueGrainAdmission.admitNative config.profile config opened.pins
        config.signature opened.durable ambient bytes with
    | .error _ => return .error "historical grain-backed application share issue refused"
    | .ok ⟨issueIngress, accepted⟩ =>
        return .ok ⟨ApplicationShareIssueGrainReceiver.intent accepted,
          .applicationGrainShareIssue accepted, some (.grain issueIngress accepted rfl),
          none, none, none, none, none, none, none, none⟩
  if let some ingress := ApplicationAgentLifetimeGrantSource.ingressCodec.decode bytes then
    match ← admitLifetimeGrantIssueAt config opened issues ingress with
    | .error detail => return .error detail
    | .ok admitted => return .ok ⟨admitted.intent,
        .applicationAgentLifetimeGrantIssue admitted, none, none, none, none, none,
        none, none, none, some ⟨ingress, ⟨admitted, rfl⟩⟩⟩
  if let some ingress := ApplicationAgentLifetimeDispatchIngress.codec.decode bytes then
    match ← admitLifetimeDispatchAt config opened grants reserves ingress with
    | .error detail => return .error detail
    | .ok admitted => return .ok admitted.toDerived
  if let some ingress := ApplicationDispatchAgentIngress.codec.decode bytes then
    match ← admitAgentDispatchAt config opened issues reserves ingress with
    | .error detail => return .error detail
    | .ok admitted => return .ok admitted.toDerived
  if let some ingress := ApplicationDispatchAdmissionIngress.codec.decode bytes then
    match ← admitDispatchAt config opened issues ingress with
    | .error detail => return .error detail
    | .ok admitted =>
        return .ok ⟨admitted.intent, .applicationDispatch admitted, none, none, none, none, none, none, none, none, none⟩
  if let some ingress := FnSelectiveReleaseSourcePublication.ingressCodec.decode bytes then
    match ← FnSelectiveReleaseSourceReceiver.admitLoaded config opened ingress with
    | .error _ => return .error "historical selected source publication admission refused"
    | .ok accepted =>
        return .ok ⟨accepted.intent config opened ingress, .selectedSourcePublication accepted, none, none, none, none, none, none, none, none, none⟩
  if let some ingress := ApplicationLifecycleCompletionV2Ingress.codec.decode bytes then
    match ← admitCompletionV2At config opened claimsV3 runningV3 ingress with
    | .error detail => return .error detail
    | .ok admitted =>
        return .ok ⟨admitted.intent, .applicationLifecycleCompletionV2 admitted,
          none, none, none, none, none, none, none,
          some ⟨ingress, ⟨admitted, rfl⟩⟩, none⟩
  if let some ingress := ApplicationLifecycleClaimV3Ingress.codec.decode bytes then
    match ← admitClaimV3At config opened beginsV3 ingress with
    | .error detail => return .error detail
    | .ok admitted =>
        return .ok ⟨admitted.intent, .applicationLifecycleClaimV3 admitted,
          none, none, none, none, none, none,
          some ⟨ingress, ⟨admitted, rfl⟩⟩, none, none⟩
  if let some ingress := ApplicationLifecycleBeginV3Ingress.codec.decode bytes then
    match ← admitBeginV3At config opened createdV3 runningV3 ingress with
    | .error detail => return .error detail
    | .ok admitted =>
        return .ok ⟨admitted.intent, .applicationLifecycleBeginV3 admitted,
          none, none, none, none, none,
          some ⟨ingress, ⟨admitted, rfl⟩⟩, none, none, none⟩
  if let some ingress := ApplicationLifecycleCompletionIngress.codec.decode bytes then
    match ← admitCompletionAt config opened claimsV2 ingress with
    | .error detail => return .error detail
    | .ok admitted => return .ok admitted.toDerived
  if let some ingress := ApplicationLifecycleClaimV2Ingress.codec.decode bytes then
    match ← admitClaimV2At config opened beginsV2 ingress with
    | .error detail => return .error detail
    | .ok admitted =>
        return .ok ⟨admitted.intent, .applicationLifecycleClaimV2 admitted,
          none, none, none, some ⟨ingress, ⟨admitted, rfl⟩⟩, none, none, none, none, none⟩
  if let some ingress := ApplicationLifecycleClaimIngress.codec.decode bytes then
    match ← admitClaimAt config opened begins ingress with
    | .error detail => return .error detail
    | .ok admitted =>
        return .ok ⟨admitted.intent, .applicationLifecycleClaim admitted, none, none, none, none, none, none, none, none, none⟩
  if let some ingress := ApplicationLifecycleBeginV2Ingress.codec.decode bytes then
    match ← ApplicationLifecycleBeginV2Admission.admitNative config.deployment
        config.profile ⟨config.federation, height⟩ config.signature opened.durable ingress with
    | .error _ => return .error "historical descriptor-bound lifecycle BEGIN refused"
    | .ok accepted =>
        return .ok ⟨accepted.intent, .applicationLifecycleBeginV2 accepted,
          none, none, some ⟨ingress, ⟨accepted, rfl⟩⟩, none, none, none, none, none, none⟩
  if let some ingress := ApplicationLifecycleBeginIngress.codec.decode bytes then
    match ← ApplicationLifecycleBeginReceiver.admitLoaded config.deployment config.profile
        ⟨config.federation, height⟩ config.signature opened.durable ingress with
    | .error _ => return .error "historical application lifecycle begin admission refused"
    | .ok accepted => return .ok ⟨accepted.intent, .applicationLifecycleBegin accepted,
        none, some ⟨ingress, ⟨accepted, rfl⟩⟩, none, none, none, none, none, none, none⟩
  if let some ingress := GrainResourceBirthPolicyController.decodeIngress bytes then
    match pinned : config.grainBirthTariffValue with
    | .error detail => return .error s!"historical grain-backed birth tariff: {detail}"
    | .ok tariff =>
        let source := ingress.source
        match GrainResourceBirthController.prepareSourceBirth config.profile.compilerProfile
            config.deployment opened.pins opened.durable config.profile.semantics tariff source with
        | .error reason => return .error s!"historical grain-backed birth preparation: {repr reason}"
        | .ok birth =>
            let ambient : DeclaredResourceController.Ambient := ⟨config.federation, height⟩
            match GrainResourceBirthTransaction.prepareTargets config.profile config.deployment
                opened.pins opened.durable ambient tariff source birth with
            | .error reason => return .error s!"historical grain target preparation: {repr reason}"
            | .ok grain =>
                match ← GrainResourceBirthAdmission.admitDecodedNative config.profile
                    config.deployment opened.pins opened.durable ambient tariff source birth grain
                    config.signature ingress with
                | .error _ => return .error "historical grain-backed birth admission refused"
                | .ok accepted =>
                    return .ok ⟨GrainResourceBirthReceiver.intent accepted,
                      .grainBirth pinned accepted, none, none, none, none, none, none, none, none, none⟩
  match ResourceBirthPolicyController.Concrete.decodeIngress bytes with
  | some ingress =>
      match ← ResourceBirthPolicyController.Concrete.admitDecodedNative config.profile config.deployment
          opened.pins config.signature opened.durable height ingress with
      | .error reason => return .error s!"birth admission refused: {repr reason}"
      | .ok accepted => return .ok ⟨ResourceBirthReceiver.intent accepted, .birth accepted, none, none, none, none, none, none, none, none, none⟩
  | none =>
    match PolicyInstallReceiver.decodeIngress bytes with
    | some ingress =>
        match ← PolicyInstallReceiver.admitDecodedNative config.profile config.deployment config.signature
            opened.durable config.federation height ingress with
        | .error reason => return .error s!"policy installation refused: {repr reason}"
        | .ok accepted => return .ok ⟨PolicyInstallReceiver.intent accepted, .install accepted, none, none, none, none, none, none, none, none, none⟩
    | none =>
      match CapabilityDelegationReceiver.decodeIngress bytes with
      | some ingress =>
          match ← CapabilityDelegationReceiver.admitDecodedNative config.deployment config.profile
              ⟨config.federation, height⟩ opened.durable config.signature ingress with
          | .error reason => return .error s!"delegation refused: {repr reason}"
          | .ok accepted => return .ok ⟨CapabilityDelegationReceiver.intent accepted, .delegate accepted, none, none, none, none, none, none, none, none, none⟩
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
                      .invoke prepared signed shape accepted, none, none, none, none,
                      some ⟨command, signed, prepared, shape, accepted, rfl⟩, none, none, none, none⟩
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

/-- A new issue enters the chronological context only after the complete
record matches the accepted intent. The caller invokes this after the durable
advance and native post-image validation have succeeded. -/
private def issuesAfter (config : Config) (opened : Opened config)
    (issues : List (PriorIssue config)) (record : DurableReceiver.IntentRecord)
    (receipt : NativeHostCodec.Receipt)
    (derived : Derived config opened)
    (matched : recordMatches record derived.intent = true) :
    List (PriorIssue config) :=
  match derived.issue with
  | none => issues
  | some (.legacy ingress accepted intentExact) =>
      let recordExact : record = DurableReceiver.IntentRecord.ofIntent
          (ApplicationShareIssueReceiver.intent accepted) := by
        rw [← intentExact]
        exact (recordMatches_iff record derived.intent).mp matched
      ⟨opened.durable.image.accepted.length, receipt,
        ApplicationDispatchHistoricalCore.IssuedEvidence.fromAccepted config opened.pins
          opened.durable (logicalHeight config opened.durable) ingress accepted record
          recordExact⟩ :: issues
  | some (.grain ingress accepted intentExact) =>
      let recordExact : record = DurableReceiver.IntentRecord.ofIntent
          (ApplicationShareIssueGrainReceiver.intent accepted) := by
        rw [← intentExact]
        exact (recordMatches_iff record derived.intent).mp matched
      ⟨opened.durable.image.accepted.length, receipt,
        ApplicationDispatchHistoricalCore.IssuedEvidence.fromGrainAccepted config opened.pins
          opened.durable ⟨config.federation, logicalHeight config opened.durable⟩
          ingress accepted record recordExact⟩ :: issues

/-- A compact ordinary invocation enters the reserve-eligible chronological
context only after the caller has matched its complete record, advanced, and
validated the successor. We retain only single-target, originally attached,
unreserved AgentGrain-shaped cells. A later event21 must still prove that its
full v2 context matches this actual signed command's nonce and reserve target. -/
private def reservesAfter (config : Config) (opened : Opened config)
    (reserves : List (PriorDispatchReserve config))
    (record : DurableReceiver.IntentRecord) (receipt : NativeHostCodec.Receipt)
    (derived : Derived config opened)
    (matched : recordMatches record derived.intent = true) :
    List (PriorDispatchReserve config) := Id.run do
  let some ordinary := derived.ordinary | return reserves
  let [target] := ordinary.command.targets | return reserves
  let .object := target.kind | return reserves
  let some observe := target.observeCapability | return reserves
  let some cell := (match opened.directory.directory.slots target.target with
    | .present cell => some cell
    | _ => none) | return reserves
  let some state := ApplicationDispatchAgentPayer.stateAt target.target cell
    | return reserves
  let some amount := (match target.payload with
    | .scalar actions => match actions[3]? with
      | some (Minidregg.Theory.DeclaredActionLowering.Action.write _ _ replacement) =>
          some replacement
      | _ => none
    | _ => none) | return reserves
  unless target == AgentGrain.Operation.target (.reserve amount)
      target.target target.capability cell.payload.root state (some observe) do
    return reserves
  if !(state.status == 1 || state.status == 2) || state.reserved != 0 ||
      target.expectedTargetRoot != cell.payload.root then
    return reserves
  let recordExact : record = DurableReceiver.IntentRecord.ofIntent
      (ordinary.accepted.dataIntent ordinary.shape) := by
    rw [← ordinary.intentExact]
    exact (recordMatches_iff record derived.intent).mp matched
  if receiptTransaction : receipt.transactionId = record.transactionId then
    if receiptEvent : receipt.eventId = record.event.eventId then
      let raw := ApplicationDispatchAgentReserveCore.RawEvidence.fromAccepted
        config opened.durable ordinary.command ordinary.signed ordinary.prepared
        ordinary.shape ordinary.accepted record receipt state cell.payload.root
        target.capability observe recordExact receiptTransaction receiptEvent
      return ⟨opened.durable.image.accepted.length, raw⟩ :: reserves
    else return reserves
  else return reserves

/-- Only a fully matched BEGIN produces a chronological certificate. The
replay caller inserts it after durable advance and post-image validation. -/
private def beginsAfter (config : Config) (opened : Opened config)
    (begins : List (PriorBegin config)) (record : DurableReceiver.IntentRecord)
    (derived : Derived config opened)
    (matched : recordMatches record derived.intent = true) :
    List (PriorBegin config) :=
  match derived.begin with
  | none => begins
  | some ⟨ingress, ⟨accepted, intentExact⟩⟩ =>
      let recordExact : record = DurableReceiver.IntentRecord.ofIntent
          accepted.intent := by
        rw [← intentExact]
        exact (recordMatches_iff record derived.intent).mp matched
      ⟨opened.durable.image.accepted.length, ingress, record,
        ⟨opened, accepted, recordExact⟩⟩ :: begins

private def beginsV2After (config : Config) (opened : Opened config)
    (begins : List (PriorBeginV2 config)) (record : DurableReceiver.IntentRecord)
    (derived : Derived config opened)
    (matched : recordMatches record derived.intent = true) :
    List (PriorBeginV2 config) :=
  match derived.beginV2 with
  | none => begins
  | some ⟨ingress, ⟨accepted, intentExact⟩⟩ =>
      let recordExact : record = DurableReceiver.IntentRecord.ofIntent
          accepted.intent := by
        rw [← intentExact]
        exact (recordMatches_iff record derived.intent).mp matched
      ⟨opened.durable.image.accepted.length, ingress, record,
        ⟨opened, accepted, recordExact⟩⟩ :: begins

/-- Called only after complete record matching, durable advance and successor
validation by `walk` or `extendExact`. This retains the actual source-admitted
v2 claim rather than inferring it from today's claimed status. -/
private def claimsV2After (config : Config) (opened : Opened config)
    (claims : List (PriorClaimV2 config)) (record : DurableReceiver.IntentRecord)
    (derived : Derived config opened)
    (matched : recordMatches record derived.intent = true) :
    List (PriorClaimV2 config) :=
  match derived.claimV2 with
  | none => claims
  | some ⟨ingress, ⟨admitted, intentExact⟩⟩ =>
      let recordExact : record = DurableReceiver.IntentRecord.ofIntent
          admitted.intent := by
        rw [← intentExact]
        exact (recordMatches_iff record derived.intent).mp matched
      ⟨opened.durable.image.accepted.length, ingress, record,
        ⟨opened, admitted, recordExact⟩⟩ :: claims

private def beginsV3After (config : Config) (opened : Opened config)
    (begins : List (PriorBeginV3 config)) (record : DurableReceiver.IntentRecord)
    (derived : Derived config opened)
    (matched : recordMatches record derived.intent = true) :
    List (PriorBeginV3 config) :=
  match derived.beginV3 with
  | none => begins
  | some ⟨ingress, ⟨admitted, intentExact⟩⟩ =>
      let recordExact : record = DurableReceiver.IntentRecord.ofIntent
          admitted.intent := by
        rw [← intentExact]
        exact (recordMatches_iff record derived.intent).mp matched
      ⟨opened.durable.image.accepted.length, ingress, record,
        ⟨opened, admitted, recordExact⟩⟩ :: begins

private def claimsV3After (config : Config) (opened : Opened config)
    (claims : List (PriorClaimV3 config)) (record : DurableReceiver.IntentRecord)
    (derived : Derived config opened)
    (matched : recordMatches record derived.intent = true) :
    List (PriorClaimV3 config) :=
  match derived.claimV3 with
  | none => claims
  | some ⟨ingress, ⟨admitted, intentExact⟩⟩ =>
      let recordExact : record = DurableReceiver.IntentRecord.ofIntent
          admitted.intent := by
        rw [← intentExact]
        exact (recordMatches_iff record derived.intent).mp matched
      ⟨opened.durable.image.accepted.length, ingress, record,
        ⟨opened, admitted, recordExact⟩⟩ :: claims

private def createdV3After (config : Config) (opened : Opened config)
    (created : List (PriorCreatedV3 config))
    (record : DurableReceiver.IntentRecord) (receipt : NativeHostCodec.Receipt)
    (derived : Derived config opened)
    (matched : recordMatches record derived.intent = true) :
    List (PriorCreatedV3 config) :=
  match derived.completionV2 with
  | none => created
  | some ⟨ingress, ⟨admitted, intentExact⟩⟩ =>
      if isCreated : ingress.creationMarker.isSome = true then
        let recordExact : record = DurableReceiver.IntentRecord.ofIntent
            admitted.intent := by
          rw [← intentExact]
          exact (recordMatches_iff record derived.intent).mp matched
        ⟨opened.durable.image.accepted.length, receipt, ingress, record,
          isCreated, ⟨opened, admitted.conditional, recordExact⟩⟩ :: created
      else created

private def runningV3After (config : Config) (opened : Opened config)
    (running : List (PriorRunningV3 config))
    (record : DurableReceiver.IntentRecord) (receipt : NativeHostCodec.Receipt)
    (derived : Derived config opened)
    (matched : recordMatches record derived.intent = true) :
    List (PriorRunningV3 config) :=
  match derived.completionV2 with
  | none => running
  | some ⟨ingress, ⟨admitted, intentExact⟩⟩ =>
      if isRunning : ingress.source.physical.report.outcome = .running then
        if isStart : ingress.source.originalBegin.base.source.kind = .start then
          let recordExact : record = DurableReceiver.IntentRecord.ofIntent
              admitted.intent := by
            rw [← intentExact]
            exact (recordMatches_iff record derived.intent).mp matched
          ⟨opened.durable.image.accepted.length, receipt, ingress, record,
            isRunning, isStart, ⟨opened, admitted.conditional, recordExact⟩⟩ :: running
        else running
      else running

private def grantsAfter (config : Config) (opened : Opened config)
    (grants : List (PriorLifetimeGrant config))
    (record : DurableReceiver.IntentRecord) (receipt : NativeHostCodec.Receipt)
    (derived : Derived config opened)
    (matched : recordMatches record derived.intent = true) :
    List (PriorLifetimeGrant config) :=
  match derived.grantIssue with
  | none => grants
  | some ⟨ingress, ⟨admitted, intentExact⟩⟩ =>
      let recordExact : record = DurableReceiver.IntentRecord.ofIntent
          admitted.intent := by
        rw [← intentExact]
        exact (recordMatches_iff record derived.intent).mp matched
      let finalRoot := (ApplicationAgentLifetimeGrantAtomicBirth.initializedWrite
        admitted.current.sourceReady).exactPost
      ⟨opened.durable.image.accepted.length, receipt, ingress, record,
        admitted.prior, finalRoot,
        ⟨opened, admitted, rfl, rfl, recordExact⟩⟩ :: grants

/-- A suffix admission cannot erase issue provenance already certified at the
old exact tip. In particular, `extendVerified` retains its old context. -/
private theorem issuesAfter_preserves_prior (config : Config) (opened : Opened config)
    (issues : List (PriorIssue config)) (record : DurableReceiver.IntentRecord)
    (receipt : NativeHostCodec.Receipt)
    (derived : Derived config opened)
    (matched : recordMatches record derived.intent = true) :
    ∀ prior, prior ∈ issues → prior ∈ issuesAfter config opened issues record receipt derived matched := by
  intro prior member
  cases issue : derived.issue with
  | none => simpa [issuesAfter, issue] using member
  | some value =>
      cases value with
      | legacy ingress accepted intentExact =>
          simp only [issuesAfter, issue]
          exact List.mem_cons_of_mem _ member
      | grain ingress accepted intentExact =>
          simp only [issuesAfter, issue]
          exact List.mem_cons_of_mem _ member

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

/-- One executable checkpoint in the same native-admitted replay walk. It
retains only this selected prefix, not every full prefix image. The prior,
selected and later traces reconstruct the exact verified records and receipts.
No caller may construct this value from a bare record index. -/
structure SelectedStep (config : Config) (origin tip : Opened config)
    (records : List DurableReceiver.IntentRecord)
    (receipts : List NativeHostCodec.Receipt) where
  priorRecords : List DurableReceiver.IntentRecord
  record : DurableReceiver.IntentRecord
  laterRecords : List DurableReceiver.IntentRecord
  priorReceipts : List NativeHostCodec.Receipt
  receipt : NativeHostCodec.Receipt
  laterReceipts : List NativeHostCodec.Receipt
  before : Opened config
  after : Opened config
  recordsExact : records = priorRecords ++ record :: laterRecords
  receiptsExact : receipts = priorReceipts ++ receipt :: laterReceipts
  priorAdmitted : AdmittedReplay config origin priorRecords before priorReceipts
  selectedAdmitted : AdmittedStep config before after record receipt
  laterAdmitted : AdmittedReplay config after laterRecords tip laterReceipts

private def SelectedStep.prepend {config : Config} {origin middle tip : Opened config}
    {record : DurableReceiver.IntentRecord}
    {later : List DurableReceiver.IntentRecord}
    {receipt : NativeHostCodec.Receipt}
    {laterReceipts : List NativeHostCodec.Receipt}
    (step : AdmittedStep config origin middle record receipt)
    (selected : SelectedStep config middle tip later laterReceipts) :
    SelectedStep config origin tip (record :: later) (receipt :: laterReceipts) :=
  ⟨record :: selected.priorRecords, selected.record, selected.laterRecords,
    receipt :: selected.priorReceipts, selected.receipt, selected.laterReceipts,
    selected.before, selected.after,
    by simpa only [List.cons_append] using congrArg (record :: ·) selected.recordsExact,
    by simpa only [List.cons_append] using congrArg (receipt :: ·) selected.receiptsExact,
    .cons step selected.priorAdmitted, selected.selectedAdmitted,
    selected.laterAdmitted⟩

private structure Walked (config : Config) (start : Opened config)
    (records : List DurableReceiver.IntentRecord) where
  final : Opened config
  receipts : List NativeHostCodec.Receipt
  trace : AdmittedReplay config start records final receipts
  selected : Option (SelectedStep config start final records receipts)
  issues : List (PriorIssue config)
  reserves : List (PriorDispatchReserve config)
  begins : List (PriorBegin config)
  beginsV2 : List (PriorBeginV2 config)
  claimsV2 : List (PriorClaimV2 config)
  frontier : FnConsumerFrontierReplay.Audit
  releases : List PriorSelectedRelease
  beginsV3 : List (PriorBeginV3 config)
  claimsV3 : List (PriorClaimV3 config)
  createdV3 : List (PriorCreatedV3 config)
  runningV3 : List (PriorRunningV3 config)
  grants : List (PriorLifetimeGrant config)

/-- Called only after the original record was natively admitted, matched in
full, advanced, and validated by this replay walk. A legacy tag9 is merely a
present-time linear anchor; old forks poison that scope rather than invalidating
the historically accepted Store. -/
private def frontierAfterLegacy (config : Config)
    (frontier : FnConsumerFrontierReplay.Audit)
    (record : DurableReceiver.IntentRecord) (receipt : NativeHostCodec.Receipt) :
    FnConsumerFrontierReplay.Audit :=
  match FnConsumerFrontierReplay.legacyTransition
      config.deployment.domain config.profile.semantics record receipt with
  | none => frontier
  | some transition => frontier.adoptLegacy record transition

/-- New event17/19 transitions are installed only after the same walk has
matched and validated their complete native-admitted durable record. -/
private def frontierAfter (config : Config)
    (frontier : FnConsumerFrontierReplay.Audit)
    (record : DurableReceiver.IntentRecord) (receipt : NativeHostCodec.Receipt) :
    Except String FnConsumerFrontierReplay.Audit := do
  if record.event.codecVersion == 20 then
    let some original := FnConsumerNamespaceHistory.selectAt
        config.deployment.domain config.profile.semantics record receipt
      | throw "fn consumer namespace retained event differs"
    frontier.register original
  else if record.event.codecVersion == 17 then
    let some ingress := FnSelectedPollCoverage.ingressCodec.decode
        record.event.canonicalBytes
      | throw "selected fn frontier retained event is noncanonical"
    unless FnSelectedPollCoverage.event ingress == record.event do
      throw "selected fn frontier retained event differs"
    frontier.advanceV2 ingress.spec.registrationReceipt
      (FnSelectedPollCoverage.transition ingress.spec receipt)
  else if record.event.codecVersion == 19 then
    let some ingress := FnEmptyPollProgressV2.ingressCodec.decode
        record.event.canonicalBytes
      | throw "empty fn frontier retained event is noncanonical"
    unless FnEmptyPollProgressV2.event ingress == record.event do
      throw "empty fn frontier retained event differs"
    frontier.advanceV2 ingress.spec.registrationReceipt
      (FnEmptyPollProgressV2.transition ingress.spec receipt)
  else
    pure (frontierAfterLegacy config frontier record receipt)

private def selectedReleaseAfter (config : Config) (after : Opened config)
    (releases : List PriorSelectedRelease)
    (record : DurableReceiver.IntentRecord) (receipt : NativeHostCodec.Receipt) :
    List PriorSelectedRelease :=
  if record.event.codecVersion == 13 &&
      (FnSelectedPollReleaseShape.selectAt config after record receipt
        record.transactionId).isSome then
    ⟨record, receipt⟩ :: releases
  else releases

private def walk (config : Config) (opened : Opened config)
    (issues : List (PriorIssue config))
    (reserves : List (PriorDispatchReserve config))
    (begins : List (PriorBegin config))
    (beginsV2 : List (PriorBeginV2 config))
    (claimsV2 : List (PriorClaimV2 config))
    (beginsV3 : List (PriorBeginV3 config))
    (claimsV3 : List (PriorClaimV3 config))
    (createdV3 : List (PriorCreatedV3 config))
    (runningV3 : List (PriorRunningV3 config))
    (grants : List (PriorLifetimeGrant config))
    (frontier : FnConsumerFrontierReplay.Audit)
    (releases : List PriorSelectedRelease)
    (selectIndex : Option Nat) :
    (records : List DurableReceiver.IntentRecord) →
    IO (Except Failure (Walked config opened records))
  | [] => pure (.ok ⟨opened, [], .nil opened, none, issues, reserves, begins, beginsV2, claimsV2,
      frontier, releases, beginsV3, claimsV3, createdV3, runningV3, grants⟩)
  | record :: rest => do
      let index := opened.durable.image.accepted.length
      match ← derive config opened issues reserves begins beginsV2 claimsV2
          beginsV3 claimsV3 createdV3 runningV3 grants frontier releases
          record.event.canonicalBytes with
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
                  index + 1, imageBoundaryCanonical config next.bytes⟩
              let nextIssues := issuesAfter config opened issues record receipt derived matched
              let nextReserves := reservesAfter config opened reserves record receipt derived matched
              let nextBegins := beginsAfter config opened begins record derived matched
              let nextBeginsV2 := beginsV2After config opened beginsV2 record derived matched
              let nextClaimsV2 := claimsV2After config opened claimsV2 record derived matched
              let nextBeginsV3 := beginsV3After config opened beginsV3 record derived matched
              let nextClaimsV3 := claimsV3After config opened claimsV3 record derived matched
              let nextCreatedV3 := createdV3After config opened createdV3 record receipt
                derived matched
              let nextRunningV3 := runningV3After config opened runningV3 record receipt
                derived matched
              let nextGrants := grantsAfter config opened grants record receipt derived matched
              let .ok nextFrontier := frontierAfter config frontier record receipt
                | return .error ⟨index, "fn consumer frontier transition refused"⟩
              let nextReleases := selectedReleaseAfter config after releases record receipt
              match ← walk config after nextIssues nextReserves nextBegins nextBeginsV2 nextClaimsV2
                  nextBeginsV3 nextClaimsV3 nextCreatedV3 nextRunningV3 nextGrants
                  nextFrontier nextReleases selectIndex rest with
              | .error failure => return .error failure
              | .ok tail =>
                let step : AdmittedStep config opened after record receipt :=
                  ⟨derived, matched, next, advanced, validated, by
                    simp only [receipt, index]
                    rw [imageBoundaryCanonical_loaded]⟩
                let selectedAt :=
                  if selectIndex == some index then
                    let selected : SelectedStep config opened tail.final
                        (record :: rest) (receipt :: tail.receipts) :=
                      ⟨[], record, rest, [], receipt, tail.receipts, opened, after,
                        by simp, by simp, .nil opened, step, tail.trace⟩
                    some selected
                  else tail.selected.map (SelectedStep.prepend step)
                return .ok ⟨tail.final, receipt :: tail.receipts,
                  .cons step tail.trace, selectedAt, tail.issues, tail.reserves, tail.begins,
                  tail.beginsV2, tail.claimsV2, tail.frontier, tail.releases,
                  tail.beginsV3, tail.claimsV3, tail.createdV3, tail.runningV3,
                  tail.grants⟩
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
  issues : List (PriorIssue config)
  reserves : List (PriorDispatchReserve config)
  begins : List (PriorBegin config)
  beginsV2 : List (PriorBeginV2 config)
  claimsV2 : List (PriorClaimV2 config)
  frontier : FnConsumerFrontierReplay.Audit
  releases : List PriorSelectedRelease
  beginsV3 : List (PriorBeginV3 config)
  claimsV3 : List (PriorClaimV3 config)
  createdV3 : List (PriorCreatedV3 config)
  runningV3 : List (PriorRunningV3 config)
  grants : List (PriorLifetimeGrant config)

/-- Per-scope current frontier minted by this exact admitted-history walk.
Ambiguous historical v1 progress refuses new ordered progress for that scope. -/
def Verified.frontierCursor {config : Config} {target : Durable}
    (verified : Verified config target) (key : FnConsumerFrontierCore.Key) :
    Except String FnConsumerFrontierCore.Cursor :=
  verified.frontier.cursor key

/-- The registration receipt and complete gateway-bound key come from this
same verified walk, not from a caller-supplied event-20 record. -/
def Verified.frontierRegistration {config : Config} {target : Durable}
    (verified : Verified config target) (key : FnConsumerFrontierCore.Key)
    (receipt : NativeHostCodec.Receipt) :
    Except String FnConsumerNamespaceHistory.Original :=
  verified.frontier.registrationFor key receipt

def Verified.frontierRegistrationAbsent {config : Config} {target : Durable}
    (verified : Verified config target)
    (consumerNamespace : FnConsumerFrontierCore.Namespace) : Bool :=
  verified.frontier.registrationAbsent consumerNamespace

/-- The optional v1 anchor must be the last unambiguous same-gateway original
retained by this verified walk. Other gateway principals cannot poison it. -/
def Verified.frontierLegacyFor {config : Config} {target : Durable}
    (verified : Verified config target) (spec : FnConsumerNamespaceRegistration.Spec) :
    Except String (Option FnConsumerNamespaceAdmissionAt.Legacy) :=
  verified.frontier.legacyFor spec

/-- Fresh admission from an exact verified tip uses its internally accumulated
issue provenance. Callers cannot supply a chronological context. The result
can feed `ExactReadback` after a receiver has prepared and read back one CAS. -/
def deriveVerified {config : Config} {target : Durable}
    (old : Verified config target) (bytes : List UInt8) :
    IO (Except String (Derived config old.opened)) :=
  derive config old.opened old.issues old.reserves old.begins old.beginsV2 old.claimsV2
    old.beginsV3 old.claimsV3 old.createdV3 old.runningV3 old.grants
    old.frontier old.releases bytes

/-- A fresh v2 BEGIN is checked on the same verified current image and then
converted to the exact native admission used by physical CAS readback. Its
descriptor and prospective manifest are mandatory in `admitNative`. -/
def admitBeginV2Verified {config : Config} {target : Durable}
    (old : Verified config target)
    (ingress : ApplicationLifecycleBeginV2Ingress.Ingress) :
    IO (Except String (ApplicationLifecycleBeginV2Admission.Accepted
      config.deployment config.profile
      ⟨config.federation, logicalHeight config old.opened.durable⟩
      old.opened.durable ingress)) :=
  ApplicationLifecycleBeginV2Admission.admitNative config.deployment config.profile
    ⟨config.federation, logicalHeight config old.opened.durable⟩
    config.signature old.opened.durable ingress

/-- The original completed-create receipt, signed custody, full event25 record
and current-prefix membership come from one verifier-minted chronology. -/
def Verified.selectCreated {config : Config} {target : Durable}
    (old : Verified config target)
    (binding : ApplicationLifecycleLaunchBinding.Binding) :
    IO (Except String (CreatedAt config old.opened binding)) :=
  selectCreatedAt config old.opened old.createdV3 binding

/-- The unit and incarnation selected for STOP come from an event25 running
completion admitted by this exact verified walk, never from the request. -/
def Verified.selectRunning {config : Config} {target : Durable}
    (old : Verified config target) (source : ApplicationLifecycleBegin.Source) :
    Except String (RunningAt config old.opened source) :=
  selectRunningAt old.opened old.runningV3 source

def admitBeginV3Verified {config : Config} {target : Durable}
    (old : Verified config target)
    (ingress : ApplicationLifecycleBeginV3Ingress.Ingress) :
    IO (Except String (Derived config old.opened)) := do
  let admitted ← match ← admitBeginV3At config old.opened old.createdV3
      old.runningV3 ingress with
    | .error detail => return .error detail
    | .ok admitted => pure admitted
  return .ok ⟨admitted.intent, .applicationLifecycleBeginV3 admitted,
    none, none, none, none, none,
    some ⟨ingress, ⟨admitted, rfl⟩⟩, none, none, none⟩

def beginV2Derived {config : Config} {target : Durable}
    (old : Verified config target)
    {ingress : ApplicationLifecycleBeginV2Ingress.Ingress}
    (accepted : ApplicationLifecycleBeginV2Admission.Accepted
      config.deployment config.profile
      ⟨config.federation, logicalHeight config old.opened.durable⟩
      old.opened.durable ingress) : Derived config old.opened :=
  ⟨accepted.intent, .applicationLifecycleBeginV2 accepted,
    none, none, some ⟨ingress, ⟨accepted, rfl⟩⟩, none, none,
    none, none, none, none⟩

def admitCompletionVerified {config : Config} {target : Durable}
    (old : Verified config target)
    (ingress : ApplicationLifecycleCompletionIngress.Ingress) :
    IO (Except String (CompletionAt config old.opened ingress)) :=
  admitCompletionAt config old.opened old.claimsV2 ingress

theorem beginV2Derived_intent {config : Config} {target : Durable}
    (old : Verified config target)
    {ingress : ApplicationLifecycleBeginV2Ingress.Ingress}
    (accepted : ApplicationLifecycleBeginV2Admission.Accepted
      config.deployment config.profile
      ⟨config.federation, logicalHeight config old.opened.durable⟩
      old.opened.durable ingress) :
    (beginV2Derived old accepted).intent = accepted.intent := rfl

/-- Fresh claim admission from an exact verified tip uses only BEGINs inserted
by that tip's admitted replay walk. It cannot manufacture historical authority
from a caller-provided physically valid image. -/
def admitClaimVerified {config : Config} {target : Durable}
    (old : Verified config target)
    (ingress : ApplicationLifecycleClaimIngress.Ingress) :
    IO (Except String (ClaimAt config old.opened ingress)) :=
  admitClaimAt config old.opened old.begins ingress

def admitClaimV2Verified {config : Config} {target : Durable}
    (old : Verified config target)
    (ingress : ApplicationLifecycleClaimV2Ingress.Ingress) :
    IO (Except String (ClaimAtV2 config old.opened ingress)) :=
  admitClaimV2At config old.opened old.beginsV2 ingress

def admitClaimV3Verified {config : Config} {target : Durable}
    (old : Verified config target)
    (ingress : ApplicationLifecycleClaimV3Ingress.Ingress) :
    IO (Except String (ClaimAtV3 config old.opened ingress)) :=
  admitClaimV3At config old.opened old.beginsV3 ingress

def admitCompletionV2Verified {config : Config} {target : Durable}
    (old : Verified config target)
    (ingress : ApplicationLifecycleCompletionV2Ingress.Ingress) :
    IO (Except String (CompletionAtV2 config old.opened ingress)) :=
  admitCompletionV2At config old.opened old.claimsV3 old.runningV3 ingress

/-- The persistent Host can admit a fresh dispatch from its exact verified tip
without replaying the whole history for every request. Only that tip's
internally accumulated issue certificates are selectable. -/
def admitDispatchVerified {config : Config} {target : Durable}
    (old : Verified config target)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) :
    IO (Except String (DispatchAt config old.opened ingress)) :=
  admitDispatchAt config old.opened old.issues ingress

/-- Event21 fresh admission reuses the verifier-minted chronological reserve
and issue contexts at one exact loaded tip. No caller can provide either. -/
def admitAgentDispatchVerified {config : Config} {target : Durable}
    (old : Verified config target)
    (ingress : ApplicationDispatchAgentIngress.Ingress) :
    IO (Except String (AgentDispatchAt config old.opened ingress)) :=
  admitAgentDispatchAt config old.opened old.issues old.reserves ingress

/-- Fresh event26 admission receives historical authority only from the exact
verified tip's ticket, initialized grant and signed v3 reserve certificates. -/
def admitLifetimeDispatchVerified {config : Config} {target : Durable}
    (old : Verified config target)
    (ingress : ApplicationAgentLifetimeDispatchIngress.Ingress) :
    IO (Except String (LifetimeDispatchAt config old.opened ingress)) :=
  admitLifetimeDispatchAt config old.opened old.grants old.reserves ingress

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

/-- The sole candidate produced from a previously verified image and the
receiver's checked `Ready`; it contains no caller-supplied post snapshot. -/
def exactCandidate {config : Config} {oldTarget : Durable}
    (old : Verified config oldTarget) (derived : Derived config old.opened)
    (ready : DurableReceiver.Ready ResourceBirthCodec.rootBytes
      old.opened.durable.image old.opened.durable.snapshot derived.intent) : Durable :=
  let image := old.opened.durable.image.append derived.intent
  ⟨DurableReceiverCodec.encode image, image, ready.next, rfl, ready.restored⟩

/-- A receiver-created exact readback carries the *complete* physical bytes.
The readback equality must come from its post-CAS byte comparison, never from a
hash or the mere `.confirmed` result, which also covers concurrent suffixes. -/
structure ExactReadback (config : Config) {oldTarget : Durable}
    (old : Verified config oldTarget) where
  derived : Derived config old.opened
  ready : DurableReceiver.Ready ResourceBirthCodec.rootBytes
    old.opened.durable.image old.opened.durable.snapshot derived.intent
  prepared : DurableReceiver.prepare old.opened.durable.image
    old.opened.durable.snapshot old.opened.durable.represented derived.intent = .inl ready
  physicalBytes : List UInt8
  exactBytes : physicalBytes = (exactCandidate old derived ready).bytes
  after : Opened config
  validated : validateLoaded config (exactCandidate old derived ready) = .ok after
  afterExact : after.durable.bytes = (exactCandidate old derived ready).bytes

/-- This is the pure proof target for a future receiving fast path: the
verifier-minted old trace plus the same admitted command's exact readback gives
one new accepted step and its *original-prefix* receipt. -/
def extendExact {config : Config} {oldTarget : Durable}
    (old : Verified config oldTarget) (readback : ExactReadback config old) :
    Verified config (exactCandidate old readback.derived readback.ready) := by
  let record := DurableReceiver.IntentRecord.ofIntent readback.derived.intent
  let target := exactCandidate old readback.derived readback.ready
  let receipt : NativeHostCodec.Receipt :=
    ⟨readback.derived.intent.transactionId, readback.derived.intent.event.eventId,
      old.opened.durable.image.accepted.length + 1, imageBoundary config target.image⟩
  have matched : recordMatches record readback.derived.intent = true := by
    exact (recordMatches_iff _ _).mpr rfl
  have step : AdmittedStep config old.opened readback.after record receipt := by
    have advanced : advance old.opened readback.derived = .ok target := by
      unfold advance
      rw [readback.prepared]
      rfl
    exact ⟨readback.derived, matched, target, advanced, readback.validated, rfl⟩
  have exactBytes : readback.after.durable.bytes = target.bytes := readback.afterExact
  have countExact : (old.receipts ++ [receipt]).length = target.image.accepted.length := by
    simp [target, exactCandidate, DurableReceiver.Image.append, old.countExact,
      ← old.image_exact]
  have admitted : AdmittedReplay config old.origin target.image.accepted
      readback.after (old.receipts ++ [receipt]) := by
    change AdmittedReplay config old.origin
      (old.opened.durable.image.accepted ++ [record]) readback.after
      (old.receipts ++ [receipt])
    rw [old.image_exact]
    exact old.admitted.append (.cons step (.nil readback.after))
  let issues := issuesAfter config old.opened old.issues record receipt readback.derived matched
  let reserves := reservesAfter config old.opened old.reserves record receipt
    readback.derived matched
  let begins := beginsAfter config old.opened old.begins record readback.derived matched
  let beginsV2 := beginsV2After config old.opened old.beginsV2
    record readback.derived matched
  let claimsV2 := claimsV2After config old.opened old.claimsV2
    record readback.derived matched
  let beginsV3 := beginsV3After config old.opened old.beginsV3
    record readback.derived matched
  let claimsV3 := claimsV3After config old.opened old.claimsV3
    record readback.derived matched
  let createdV3 := createdV3After config old.opened old.createdV3
    record receipt readback.derived matched
  let runningV3 := runningV3After config old.opened old.runningV3
    record receipt readback.derived matched
  let grants := grantsAfter config old.opened old.grants
    record receipt readback.derived matched
  -- Existing exact-readback callers are non-frontier operations. If a future
  -- caller extends a frontier event whose transition unexpectedly fails,
  -- poison all frontier projections rather than keeping the prior cursor.
  -- Full `verifyLoaded` rejects the invalid transition outright.
  let frontier := match frontierAfter config old.frontier record receipt with
    | .ok next => next
    | .error _ => { old.frontier with fault := true }
  let releases := selectedReleaseAfter config readback.after old.releases record receipt
  exact ⟨old.origin, readback.after, exactBytes, old.receipts ++ [receipt], countExact,
    admitted, issues, reserves, begins, beginsV2, claimsV2, frontier, releases,
    beginsV3, claimsV3, createdV3, runningV3, grants⟩

/-- Exact readback keeps the original accepted-prefix receipt, even when a
subsequent current tip will contain more accepted entries. -/
theorem extendExact_receipts {config : Config} {oldTarget : Durable}
    (old : Verified config oldTarget) (readback : ExactReadback config old) :
    (extendExact old readback).receipts = old.receipts ++
      [⟨readback.derived.intent.transactionId, readback.derived.intent.event.eventId,
        old.opened.durable.image.accepted.length + 1,
        imageBoundary config (exactCandidate old readback.derived readback.ready).image⟩] := by
  rfl

/-- The newly verified target is byte-for-byte the physical post-CAS readback.
This is stronger than equal height, state root, or transaction digest. -/
theorem extendExact_physicalBytes {config : Config} {oldTarget : Durable}
    (old : Verified config oldTarget) (readback : ExactReadback config old) :
    (extendExact old readback).opened.durable.bytes = readback.physicalBytes := by
  exact (extendExact old readback).exactBytes.trans readback.exactBytes.symm

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
      match ← walk config opened [] [] [] [] [] [] [] [] [] [] {} [] none target.image.accepted with
      | .error failure => return .error failure
      | .ok walked =>
        if exactBytes : walked.final.durable.bytes = target.bytes then
          if countExact : walked.receipts.length = target.image.accepted.length then
            return .ok ⟨opened, walked.final, exactBytes, walked.receipts,
              countExact, walked.trace, walked.issues, walked.reserves, walked.begins,
              walked.beginsV2, walked.claimsV2, walked.frontier, walked.releases,
              walked.beginsV3, walked.claimsV3, walked.createdV3,
              walked.runningV3, walked.grants⟩
          else return .error ⟨target.image.accepted.length, "verified history count mismatch"⟩
        else return .error ⟨target.image.accepted.length, "verified canonical tip mismatch"⟩

/-- A single verified replay pass retains exactly one executable historical
checkpoint. Its `before` is the actual admitted prefix consumed by `derive`,
not an independently reconstructed physically valid image. The selected
record and receipt are included in the exact verified tip. -/
structure VerifiedSelection (config : Config) (target : Durable) (index : Nat) where
  private mk ::
  verified : Verified config target
  selected : SelectedStep config verified.origin verified.opened
    target.image.accepted verified.receipts
  indexExact : selected.priorRecords.length = index

theorem VerifiedSelection.record_at {config : Config} {target : Durable} {index : Nat}
    (selection : VerifiedSelection config target index) :
    target.image.accepted[index]? = some selection.selected.record := by
  calc
    target.image.accepted[index]? =
        (selection.selected.priorRecords ++
          selection.selected.record :: selection.selected.laterRecords)[index]? :=
      congrArg (fun records : List DurableReceiver.IntentRecord => records[index]?)
        selection.selected.recordsExact
    _ = some selection.selected.record := by
      have atPrior :
          (selection.selected.priorRecords ++
            selection.selected.record :: selection.selected.laterRecords)[selection.selected.priorRecords.length]? =
            some selection.selected.record := by simp
      simpa only [selection.indexExact] using atPrior

/-- A requested checkpoint outside the verified history refuses. No replay
prefixes other than this one are retained; ordinary `verifyLoaded` and suffix
verification continue without a selected checkpoint. -/
def verifyLoadedSelected (config : Config) (target : Durable) (index : Nat) :
    IO (Except Failure (VerifiedSelection config target index)) := do
  if !(index < target.image.accepted.length) then
    return .error ⟨index, "selected accepted history index unavailable"⟩
  let genesis : DurableReceiver.Image := ⟨target.image.seed, []⟩
  match DurableReceiverIO.loadBytes rootBytes (DurableReceiverCodec.encode genesis) with
  | .error detail => return .error ⟨0, s!"genesis decoding: {detail}"⟩
  | .ok initial =>
    match validateLoaded config initial with
    | .error detail => return .error ⟨0, s!"pinned genesis: {detail}"⟩
    | .ok opened =>
      match ← walk config opened [] [] [] [] [] [] [] [] [] [] {} [] (some index) target.image.accepted with
      | .error failure => return .error failure
      | .ok walked =>
        if exactBytes : walked.final.durable.bytes = target.bytes then
          if countExact : walked.receipts.length = target.image.accepted.length then
            match walked.selected with
            | none => return .error ⟨index, "selected native checkpoint unavailable"⟩
            | some selected =>
              if indexExact : selected.priorRecords.length = index then
                let verified : Verified config target :=
                  ⟨opened, walked.final, exactBytes, walked.receipts,
                    countExact, walked.trace, walked.issues, walked.reserves, walked.begins,
                    walked.beginsV2, walked.claimsV2, walked.frontier, walked.releases,
                    walked.beginsV3, walked.claimsV3, walked.createdV3,
                    walked.runningV3, walked.grants⟩
                return .ok ⟨verified, selected, indexExact⟩
              else return .error ⟨index, "selected native checkpoint index mismatch"⟩
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
    match ← walk config old.opened old.issues old.reserves old.begins old.beginsV2 old.claimsV2
        old.beginsV3 old.claimsV3 old.createdV3 old.runningV3 old.grants
        old.frontier old.releases none suffix with
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
          return .ok ⟨old.origin, walked.final, exactBytes, receipts, countExact,
            admitted, walked.issues, walked.reserves, walked.begins, walked.beginsV2, walked.claimsV2,
            walked.frontier, walked.releases, walked.beginsV3, walked.claimsV3,
            walked.createdV3, walked.runningV3, walked.grants⟩
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
#print axioms Minidregg.Kernel.NativeHostReplay.extendExact
#print axioms Minidregg.Kernel.NativeHostReplay.extendExact_receipts
#print axioms Minidregg.Kernel.NativeHostReplay.extendExact_physicalBytes
