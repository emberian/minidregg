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
import Kernel.ApplicationShareIssueReceiver
import Kernel.ApplicationDispatchHistoricalCore

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
  evidence : ApplicationDispatchHistoricalCore.IssuedEvidence config

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
  | applicationDispatch {ingress : ApplicationDispatchAdmissionIngress.Ingress}
      (admitted : DispatchAt config opened ingress) :
      NativeAdmission config opened admitted.intent
  | selectedSourcePublication {ingress : FnSelectiveReleaseSourcePublication.Ingress}
      (accepted : FnSelectiveReleaseSourceReceiver.Accepted config opened ingress) :
      NativeAdmission config opened (accepted.intent config opened ingress)
  | applicationLifecycleBegin {ingress : ApplicationLifecycleBeginIngress.Ingress}
      (accepted : ApplicationLifecycleBeginReceiver.Accepted config.deployment config.profile
        ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable ingress) :
      NativeAdmission config opened accepted.intent

structure Derived (config : Config) (opened : Opened config) where
  private mk ::
  intent : DataIntent rootBytes
  admission : NativeAdmission config opened intent
  issue : Option (Σ ingress : ApplicationShareIssueSource.Ingress,
    { accepted : ApplicationShareIssueAdmission.Accepted config.profile config opened.pins
        opened.durable (logicalHeight config opened.durable) ingress //
      intent = ApplicationShareIssueReceiver.intent accepted })

/-- Reuse the very same typed dispatch admission for the exact CAS readback
fast path. No second signature check or caller-created Derived is needed. -/
def DispatchAt.toDerived {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : DispatchAt config opened ingress) : Derived config opened :=
  ⟨admitted.intent, .applicationDispatch admitted, none⟩

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
      ApplicationShareIssueSource.ingressCodec.encode issue.evidence.ingress))

/-- A dispatch before any admitted issue has no historical source to select. -/
private theorem priorIssueFor_empty (config : Config)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) :
    priorIssueFor config [] ingress = none := rfl

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

/-- Fresh native admission is mandatory even if the final image contains an
identical receipt. The issue context is private to the chronological replay
walk; no caller-provided signed issue bytes can populate it. -/
private def derive (config : Config) (opened : Opened config)
    (issues : List (PriorIssue config)) (bytes : List UInt8) :
    IO (Except String (Derived config opened)) := do
  let height := logicalHeight config opened.durable
  if let some ingress := CapabilityRevocationReceiver.decodeIngress bytes then
    match ← CapabilityRevocationReceiver.admitDecodedNative config.deployment config.profile
        ⟨config.federation, height⟩ opened.durable config.signature ingress with
    | .error reason => return .error s!"revocation refused: {repr reason}"
    | .ok accepted => return .ok ⟨CapabilityRevocationReceiver.intent accepted, .revoke accepted, none⟩
  if let some ingress := FnSelectiveReleaseIngress.ingressCodec.decode bytes then
    match ← FnSelectiveReleaseAdmission.admit config opened ingress with
    | .error _ => return .error "historical selected release admission refused"
    | .ok accepted =>
        return .ok ⟨accepted.intent config opened ingress, .selectiveRelease accepted, none⟩
  if (ApplicationShareIssueSource.ingressCodec.decode bytes).isSome then
    match ← ApplicationShareIssueAdmission.admitNative config.profile config opened.pins
        config.signature opened.durable height bytes with
    | .error _ => return .error "historical application share issue admission refused"
    | .ok ⟨issueIngress, accepted⟩ =>
        return .ok ⟨ApplicationShareIssueReceiver.intent accepted,
          .applicationShareIssue accepted, some ⟨issueIngress, ⟨accepted, rfl⟩⟩⟩
  if let some ingress := ApplicationDispatchAdmissionIngress.codec.decode bytes then
    match ← admitDispatchAt config opened issues ingress with
    | .error detail => return .error detail
    | .ok admitted =>
        return .ok ⟨admitted.intent, .applicationDispatch admitted, none⟩
  if let some ingress := FnSelectiveReleaseSourcePublication.ingressCodec.decode bytes then
    match ← FnSelectiveReleaseSourceReceiver.admitLoaded config opened ingress with
    | .error _ => return .error "historical selected source publication admission refused"
    | .ok accepted =>
        return .ok ⟨accepted.intent config opened ingress, .selectedSourcePublication accepted, none⟩
  if let some ingress := ApplicationLifecycleBeginIngress.codec.decode bytes then
    match ← ApplicationLifecycleBeginReceiver.admitLoaded config.deployment config.profile
        ⟨config.federation, height⟩ config.signature opened.durable ingress with
    | .error _ => return .error "historical application lifecycle begin admission refused"
    | .ok accepted => return .ok ⟨accepted.intent, .applicationLifecycleBegin accepted, none⟩
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
                      .grainBirth pinned accepted, none⟩
  match ResourceBirthPolicyController.Concrete.decodeIngress bytes with
  | some ingress =>
      match ← ResourceBirthPolicyController.Concrete.admitDecodedNative config.profile config.deployment
          opened.pins config.signature opened.durable height ingress with
      | .error reason => return .error s!"birth admission refused: {repr reason}"
      | .ok accepted => return .ok ⟨ResourceBirthReceiver.intent accepted, .birth accepted, none⟩
  | none =>
    match PolicyInstallReceiver.decodeIngress bytes with
    | some ingress =>
        match ← PolicyInstallReceiver.admitDecodedNative config.profile config.deployment config.signature
            opened.durable config.federation height ingress with
        | .error reason => return .error s!"policy installation refused: {repr reason}"
        | .ok accepted => return .ok ⟨PolicyInstallReceiver.intent accepted, .install accepted, none⟩
    | none =>
      match CapabilityDelegationReceiver.decodeIngress bytes with
      | some ingress =>
          match ← CapabilityDelegationReceiver.admitDecodedNative config.deployment config.profile
              ⟨config.federation, height⟩ opened.durable config.signature ingress with
          | .error reason => return .error s!"delegation refused: {repr reason}"
          | .ok accepted => return .ok ⟨CapabilityDelegationReceiver.intent accepted, .delegate accepted, none⟩
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
                      .invoke prepared signed shape accepted, none⟩
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
    (derived : Derived config opened)
    (matched : recordMatches record derived.intent = true) :
    List (PriorIssue config) :=
  match derived.issue with
  | none => issues
  | some ⟨ingress, ⟨accepted, intentExact⟩⟩ =>
      let recordExact : record = DurableReceiver.IntentRecord.ofIntent
          (ApplicationShareIssueReceiver.intent accepted) := by
        rw [← intentExact]
        exact (recordMatches_iff record derived.intent).mp matched
      ⟨opened.durable.image.accepted.length,
        ApplicationDispatchHistoricalCore.IssuedEvidence.fromAccepted config opened.pins
          opened.durable (logicalHeight config opened.durable) ingress accepted record
          recordExact⟩ :: issues

/-- A suffix admission cannot erase issue provenance already certified at the
old exact tip. In particular, `extendVerified` retains its old context. -/
private theorem issuesAfter_preserves_prior (config : Config) (opened : Opened config)
    (issues : List (PriorIssue config)) (record : DurableReceiver.IntentRecord)
    (derived : Derived config opened)
    (matched : recordMatches record derived.intent = true) :
    ∀ prior, prior ∈ issues → prior ∈ issuesAfter config opened issues record derived matched := by
  intro prior member
  cases issue : derived.issue with
  | none => simpa [issuesAfter, issue] using member
  | some value =>
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

private def walk (config : Config) (opened : Opened config)
    (issues : List (PriorIssue config)) (selectIndex : Option Nat) :
    (records : List DurableReceiver.IntentRecord) →
    IO (Except Failure (Walked config opened records))
  | [] => pure (.ok ⟨opened, [], .nil opened, none, issues⟩)
  | record :: rest => do
      let index := opened.durable.image.accepted.length
      match ← derive config opened issues record.event.canonicalBytes with
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
              let nextIssues := issuesAfter config opened issues record derived matched
              match ← walk config after nextIssues selectIndex rest with
              | .error failure => return .error failure
              | .ok tail =>
                let step : AdmittedStep config opened after record receipt :=
                  ⟨derived, matched, next, advanced, validated, rfl⟩
                let selectedAt :=
                  if selectIndex == some index then
                    let selected : SelectedStep config opened tail.final
                        (record :: rest) (receipt :: tail.receipts) :=
                      ⟨[], record, rest, [], receipt, tail.receipts, opened, after,
                        by simp, by simp, .nil opened, step, tail.trace⟩
                    some selected
                  else tail.selected.map (SelectedStep.prepend step)
                return .ok ⟨tail.final, receipt :: tail.receipts,
                  .cons step tail.trace, selectedAt, tail.issues⟩
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

/-- Fresh admission from an exact verified tip uses its internally accumulated
issue provenance. Callers cannot supply a chronological context. The result
can feed `ExactReadback` after a receiver has prepared and read back one CAS. -/
def deriveVerified {config : Config} {target : Durable}
    (old : Verified config target) (bytes : List UInt8) :
    IO (Except String (Derived config old.opened)) :=
  derive config old.opened old.issues bytes

/-- The persistent Host can admit a fresh dispatch from its exact verified tip
without replaying the whole history for every request. Only that tip's
internally accumulated issue certificates are selectable. -/
def admitDispatchVerified {config : Config} {target : Durable}
    (old : Verified config target)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) :
    IO (Except String (DispatchAt config old.opened ingress)) :=
  admitDispatchAt config old.opened old.issues ingress

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
  let issues := issuesAfter config old.opened old.issues record readback.derived matched
  exact ⟨old.origin, readback.after, exactBytes, old.receipts ++ [receipt], countExact,
    admitted, issues⟩

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
      match ← walk config opened [] none target.image.accepted with
      | .error failure => return .error failure
      | .ok walked =>
        if exactBytes : walked.final.durable.bytes = target.bytes then
          if countExact : walked.receipts.length = target.image.accepted.length then
            return .ok ⟨opened, walked.final, exactBytes, walked.receipts,
              countExact, walked.trace, walked.issues⟩
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
      match ← walk config opened [] (some index) target.image.accepted with
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
                    countExact, walked.trace, walked.issues⟩
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
    match ← walk config old.opened old.issues none suffix with
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
            admitted, walked.issues⟩
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
