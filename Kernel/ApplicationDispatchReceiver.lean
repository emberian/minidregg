/-
Fresh physical dispatch receiving. The only permit-producing branch is a new
special event 11 committed by CAS and confirmed against the exact complete
post-image bytes. Historical receipt recovery, generic DRC event 3, a
concurrent suffix, and an uncertain CAS response are not delivery permits.
-/
module

public import Compiler.ApplicationReceivingDomain
public import Kernel.ApplicationDispatchProjection
public import Kernel.ApplicationDispatchLookup
public import Kernel.ApplicationRouteAdmission
public import Kernel.NativeHostLight

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Kernel.ApplicationDispatchReceiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- A distinct wire frame ensures the physical host cannot confuse a checked
candidate with an actually committed dispatch permit. The host accepts this
frame only from its fixed native process, never from client HTTP bytes. -/
private def permitCodec : LawfulCodec
    (ApplicationDispatchProjection.Candidate × NativeHostCodec.Receipt) :=
  NativeHostCodec.framed
    ApplicationReceivingDomain.dispatchCommittedPermitFrame
    (StreamCodec.product ApplicationDispatchProjection.candidateStream
      NativeHostCodec.receiptStream)

/-- Strict read-only inspection of a committed-frame shape. Decoding bytes
does not establish CAS provenance: only `Permit.withFreshTip` may supply this
frame to the physical host's private op34 response channel. -/
def inspectCommittedBytes (bytes : List UInt8) :
    Option (ApplicationDispatchProjection.Candidate × NativeHostCodec.Receipt) :=
  permitCodec.decode bytes

/-- The fresh private response uses a distinct exact tag/payload. A native
receiver may retire only this attempt's matching active marker on this verdict;
ordinary outcomes and transport errors are not equivalent evidence. -/
def noRecordRefusalBytes : List UInt8 :=
  ApplicationReceivingDomain.noRecordRefusalFrame

/-- Positive exact-call absence at one authenticated current image. The
token retains the full-history Verified witness, so an unchecked Opened
image cannot mint this verdict. It also keeps the canonical command selection
rather than trusting a plan label.
It is emitted only after a fresh physical-tip callback. -/
structure RefusalAtTip (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) where
  private mk ::
  selected : ApplicationDispatchCommand.Selection
  selectionExact : ApplicationDispatchAdmission.selectCommand ingress = some selected
  absent : old.opened.durable.image.accepted.findIdx? (fun record =>
    record.transactionId == DeclaredResourceController.transactionId ingress.dispatch.domain
      ingress.dispatch.semantics
      (ApplicationDispatchCommand.command ingress.dispatch selected ingress.parent)) = none

def refusalAtTip? {config : Config} {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) :
    Option (RefusalAtTip config old ingress) :=
  match selected : ApplicationDispatchAdmission.selectCommand ingress with
  | none => none
  | some selection =>
      -- The call's transaction id once, then the Store's cached first-index
      -- table (`Loaded.firstIndex_eq`), never a re-derivation per accepted record.
      let transactionId := DeclaredResourceController.transactionId ingress.dispatch.domain
        ingress.dispatch.semantics (ApplicationDispatchCommand.command ingress.dispatch selection ingress.parent)
      if absent : old.opened.durable.firstIndex transactionId = none then
        some ⟨selection, selected, by rw [← DurableReceiverIO.Loaded.firstIndex_eq]; exact absent⟩
      else none

/-- A private resident's immutable route constraint. This grants no authority;
current signed dispatch admission remains mandatory. The distinct envelope
prevents accidental interpretation as an ordinary op34 request. -/
structure RouteConstraint where
  domain : Digest
  semantics : Digest
  binding : ApplicationStreamContinuity.Binding
  deriving DecidableEq

def routeConstraintStream : StreamCodec RouteConstraint :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      ApplicationStreamContinuity.bindingStream))
    (fun c => (c.domain, c.semantics, c.binding))
    (fun (domain, semantics, binding) => ⟨domain, semantics, binding⟩)
    (by intro c; cases c; rfl)

def routeBoundCodec : LawfulCodec (RouteConstraint × List UInt8) :=
  NativeHostCodec.framed
    ApplicationReceivingDomain.routeBoundDispatchFrame
    (StreamCodec.product routeConstraintStream bytesStream)

/-! ## The light route (KN2 2b)

The dispatch admits on the light ground of its keys at the opening's head; its issue is read
from the Store's history by its source bytes and re-admitted at its own prefix
(`NativeHostReplay.selectIssueByBytes`); the commit is `DurableServed.receiveServed`. -/

/-- The keys a dispatch's current admission reads beyond the state: its selected command's
transaction id and operation marker (`DeclaredResourceController.invocationKeys`) and the
dispatch's own replay nullifier. -/
def lightKeys (ingress : ApplicationDispatchAdmissionIngress.Ingress) : DurableView.Keys :=
  match ApplicationDispatchAdmission.selectCommand ingress with
  | none => ⟨[], [ApplicationDispatchAdmissionIngress.nullifier ingress]⟩
  | some selection =>
      let current := DeclaredResourceController.invocationKeys ingress.dispatch.domain ingress.dispatch.semantics
        (ApplicationDispatchCommand.command ingress.dispatch selection ingress.parent)
      ⟨current.transactions, current.nullifiers ++ [ApplicationDispatchAdmissionIngress.nullifier ingress]⟩

/-- A dispatch committed on the light route: its issue selected from the Store's history at
`issueIndex` by its source bytes and re-admitted at its own prefix, the current dispatch checked
on the light ground at the opening's head for that issue, its transaction verified unrecorded
there, and the appended record exactly its intent's. -/
structure LightCommitted (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes) where
  private mk ::
  ingress : ApplicationDispatchAdmissionIngress.Ingress
  grounded : ServedBasis.Grounded config.deployment opening.head
  issueIndex : Nat
  issue : NativeHostReplay.IssueSelected config opening.head issueIndex
  checked : ApplicationDispatchHistoricalCore.CheckedCandidate config grounded.ground ingress issue.evidence
  fresh : grounded.ground.recorded (ApplicationDispatchPending.candidateIntent checked.checked).transactionId =
    some none
  kind : DurableReceiverIO.Confirmation
  next : DurableServed.Opening ResourceBirthCodec.rootBytes
  height : next.head.height = opening.head.height + 1
  entry : DurableReceiverIO.Entry
  entryExact : entry.record = DurableCheckpointCodec.recordFrame.encode
    (DurableReceiver.IntentRecord.ofIntent (ApplicationDispatchPending.candidateIntent checked.checked))
  /-- This attempt's own append installed the entry (`Received.appended`'s `fresh`). -/
  freshCasWinner : Bool

namespace LightCommitted

variable {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}

def intent (committed : LightCommitted config opening) : DurableDataIntent.DataIntent ResourceBirthCodec.rootBytes :=
  ApplicationDispatchPending.candidateIntent committed.checked.checked

def projection (committed : LightCommitted config opening) : ApplicationDispatchProjection.Candidate :=
  ApplicationDispatchProjection.ofChecked committed.checked

def receipt (committed : LightCommitted config opening) : NativeHostCodec.Receipt :=
  ⟨committed.intent.transactionId, committed.intent.event.eventId, committed.next.head.height,
    committed.next.served.worldRoot⟩

/-- **What a light dispatch commit proves**: the appended record is the checked dispatch's
intent's, written as the opening's next record; the record verified under the opening's head at
the issue's height is the issue re-admitted at its own prefix, whose source bytes the dispatch
names; the issued ticket is live and the issuer lineage current on the light ground; the
dispatch's transaction id was verified unrecorded there. -/
theorem exact (committed : LightCommitted config opening) :
    committed.entry.record = DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent committed.intent) ∧
      committed.next.head.height = opening.head.height + 1 ∧
      (∃ read : DurableHistoryReader.Record opening.head (committed.issueIndex + 1),
        read.record = committed.issue.evidence.record) ∧
      committed.ingress.issueIngressBytes = committed.issue.evidence.ingressBytes ∧
      committed.checked.checked.ticket.liveAt (config.genesisHeight + committed.grounded.ground.height) = true ∧
      committed.grounded.ground.recorded committed.intent.transactionId = some none :=
  ⟨committed.entryExact, committed.height, committed.issue.read_evidence,
    committed.checked.issuer_current.1, committed.checked.issuer_current.2.1, committed.fresh⟩

end LightCommitted

/-- Delivery authority on the light route: this attempt freshly won and installed the CAS. -/
structure LightPermit (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes)
    extends LightCommitted config opening where
  private mk ::
  fresh : toLightCommitted.freshCasWinner = true
  installed : toLightCommitted.kind = .installed

/-- **What a light permit proves**: this attempt's own append installed the entry, and that entry
is the committed dispatch's (`LightCommitted.exact`). -/
theorem LightPermit.won_fresh_installed {config : Config}
    {opening : DurableServed.Opening ResourceBirthCodec.rootBytes} (permit : LightPermit config opening) :
    permit.freshCasWinner = true ∧ permit.kind = .installed ∧
      permit.entry.record = DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent permit.toLightCommitted.intent) :=
  ⟨permit.fresh, permit.installed, permit.entryExact⟩

/-- The committed frame, offered only while the Store's tip is still exactly this permit's entry. -/
def LightPermit.withFreshTip {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    {α : Type} (permit : LightPermit config opening) (transport : DurableReceiverIO.Transport)
    (handoff : List UInt8 → IO α) : IO (Except String α) := do
  let .ok current ← DurableReceiverIO.tipIs transport permit.next.head.height permit.entry
    | return .error "dispatch physical tip unavailable before handoff"
  if current then
    return .ok (← handoff (permitCodec.encode (permit.projection, permit.receipt)))
  else return .error "dispatch physical tip changed before handoff"

/-- Positive exact-call absence under the opening's head: the call's transaction id opens to
no row of the head's index. Emitted only after a fresh physical-tip callback. -/
structure LightRefusal (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) where
  private mk ::
  transactionId : Digest
  transactionExact : ApplicationDispatchLookup.callTransaction ingress = some transactionId
  absent : DurableIndex.Opens opening.head.indexRoot (DurableIndex.transactionKey transactionId) none

/-- **What a light refusal proves**: the transaction id of the exact call the ingress names opens
to no row of the opening head's index (the call is absent from that history). -/
theorem LightRefusal.exact {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress} (refusal : LightRefusal config opening ingress) :
    ApplicationDispatchLookup.callTransaction ingress = some refusal.transactionId ∧
      DurableIndex.Opens opening.head.indexRoot (DurableIndex.transactionKey refusal.transactionId) none :=
  ⟨refusal.transactionExact, refusal.absent⟩

def LightRefusal.withFreshTip {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress} {α : Type}
    (_refusal : LightRefusal config opening ingress) (transport : DurableReceiverIO.Transport)
    (handoff : List UInt8 → IO α) : IO (Except String α) :=
  opening.withFreshTip transport (handoff noRecordRefusalBytes)

inductive LightResult (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes) where
  | permitted (permit : LightPermit config opening)
  | committed (committed : LightCommitted config opening)
  | historical (receipt : NativeHostCodec.Receipt)
  | rejected (detail : String)
  /-- Positive call absence, emitted only while the same physical tip is current. -/
  | noRecordRefused {ingress : ApplicationDispatchAdmissionIngress.Ingress}
      (refusal : LightRefusal config opening ingress)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

/-- Only this attempt's own install gets a permit; a readback after `.alreadyPresent` or an
uncertain response is receipt evidence only. -/
def LightCommitted.result {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    (committed : LightCommitted config opening) : LightResult config opening :=
  if fresh : committed.freshCasWinner = true then
    if installed : committed.kind = .installed then .permitted ⟨committed, fresh, installed⟩
    else .committed committed
  else .committed committed

theorem light_nonwinner_receipt_only {config : Config}
    {opening : DurableServed.Opening ResourceBirthCodec.rootBytes} (committed : LightCommitted config opening)
    (notFresh : committed.freshCasWinner = false) : committed.result = .committed committed := by
  simp [LightCommitted.result, notFresh]

theorem light_recovered_receipt_only {config : Config}
    {opening : DurableServed.Opening ResourceBirthCodec.rootBytes} (committed : LightCommitted config opening)
    (recovered : committed.kind = .recoveredAfterUncertainResponse) :
    committed.result = .committed committed := by
  simp [LightCommitted.result, recovered]

def lightRouteMatches (config : Config) {ground : DeclaredResourceController.Ground config.deployment}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    {issued : ApplicationDispatchHistoricalCore.IssuedEvidence config}
    (candidate : ApplicationDispatchHistoricalCore.CheckedCandidate config ground ingress issued)
    (constraint : RouteConstraint) : Bool :=
  constraint.domain == config.deployment.domain &&
    constraint.semantics == config.profile.semantics &&
    constraint.binding == ApplicationStreamContinuity.bindingOf candidate

/-- The commit of a checked dispatch: the route constraint against that same candidate, the
freshness of its transaction id on its ground, then the CAS. -/
def commitChecked (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (constraint : Option RouteConstraint) (refusal : LightRefusal config light.opening ingress)
    (grounded : ServedBasis.Grounded config.deployment light.opening.head) (issueIndex : Nat)
    (issue : NativeHostReplay.IssueSelected config light.opening.head issueIndex)
    (checked : ApplicationDispatchHistoricalCore.CheckedCandidate config grounded.ground ingress issue.evidence)
    (adopt : NativeHostLight.Adopt) : IO (LightResult config light.opening) := do
  if constraint.isSome && !(constraint.all (lightRouteMatches config checked)) then
    return .noRecordRefused refusal
  match fresh : grounded.ground.recorded (ApplicationDispatchPending.candidateIntent checked.checked).transactionId with
  | none => return .rejected "dispatch transaction identity undeclared"
  | some (some _) => return .rejected "dispatch transaction identity already used"
  | some none =>
      match ← DurableServed.receiveServed transport ResourceBirthCodec.rootBytes light.opening
          (ApplicationDispatchPending.candidateIntent checked.checked) with
      | .appended kind next height entry entryExact freshCasWinner =>
          adopt next none
          let committed : LightCommitted config light.opening :=
            ⟨ingress, grounded, issueIndex, issue, checked, fresh, kind, next, height, entry, entryExact,
              freshCasWinner⟩
          return committed.result
      -- Recorded between the lookup and the append: the lookup answers on retry.
      | .replayed _ => return .contention
      | .rejected reason => return .rejected s!"durable dispatch refused: {repr reason}"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

/-- **A mismatched locally registered route cannot invoke the durable receiver**, create a
delivery permit or bill a dispatch: the commit of a checked candidate whose binding differs from
the route constraint is the call's absence, with no other effect. -/
theorem light_mismatched_route_never_submits (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (constraint : RouteConstraint) (refusal : LightRefusal config light.opening ingress)
    (grounded : ServedBasis.Grounded config.deployment light.opening.head) (issueIndex : Nat)
    (issue : NativeHostReplay.IssueSelected config light.opening.head issueIndex)
    (checked : ApplicationDispatchHistoricalCore.CheckedCandidate config grounded.ground ingress issue.evidence)
    (adopt : NativeHostLight.Adopt) (mismatch : lightRouteMatches config checked constraint = false) :
    commitChecked config transport light ingress (some constraint) refusal grounded issueIndex issue checked adopt =
      pure (.noRecordRefused refusal) := by
  simp [commitChecked, mismatch]

/-- The admission after the gates: the issue by its source bytes, the current dispatch on the
light ground of its keys, then `commitChecked`. A history read failure is unavailable (never the
call's absence); a refused issue or current admission is the call's absence. -/
def receiveServedAdmitted (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (constraint : Option RouteConstraint) (refusal : LightRefusal config light.opening ingress)
    (adopt : NativeHostLight.Adopt) : IO (LightResult config light.opening) := do
  let reader := light.opening.reader transport ResourceBirthCodec.rootBytes
  let grounded ← match ← light.groundedVia transport (lightKeys ingress) with
    | .error detail => return .unavailable detail
    | .ok grounded => pure grounded
  let ⟨issueIndex, issue, _⟩ ← match ← NativeHostReplay.selectIssueByBytes config reader light.opened.pins
      grounded.ground.height ingress.issueIngressBytes with
    | .error (.history detail) => return .unavailable detail
    | .error (.refused _) => return .noRecordRefused refusal
    | .ok selected => pure selected
  let checked ← match ← ApplicationDispatchHistoricalCore.checkCurrent config grounded.ground ingress
      issue.evidence with
    | .error _ => return .noRecordRefused refusal
    | .ok checked => pure checked
  commitChecked config transport light ingress constraint refusal grounded issueIndex issue checked adopt

/-- **The light dispatch**: a recorded call answers by its original receipt (`lookupLight`)
before any current-law check; an absent one is checked for the reserved probes and the session
origin (both refused with the call's absence), then admitted and committed
(`receiveServedAdmitted`). -/
def receiveServedWith (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (bytes : List UInt8) (constraint : Option RouteConstraint)
    (adopt : NativeHostLight.Adopt) : IO (LightResult config light.opening) := do
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode bytes
    | return .rejected "noncanonical special dispatch ingress"
  match transactionExact : ApplicationDispatchLookup.callTransaction ingress with
  | none => return .rejected "dispatch exact-call absence unavailable"
  | some transactionId =>
      match ← ApplicationDispatchLookup.lookupLight (light.opening.reader transport ResourceBirthCodec.rootBytes)
          ingress transactionId with
      | .error _ => return .rejected "dispatch historical identity unavailable or conflicting"
      | .ok (.historical receipt) => return .historical receipt
      | .ok (.absent absent) =>
          let refusal : LightRefusal config light.opening ingress := ⟨transactionId, transactionExact, absent⟩
          if ApplicationStreamContinuity.reservedProbe ingress.dispatch.dispatch.request then
            return .noRecordRefused refusal
          if ingress.dispatch.dispatch.session.origin != .human then
            return .noRecordRefused refusal
          receiveServedAdmitted config transport light ingress constraint refusal adopt

def receiveServed (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (bytes : List UInt8)
    (adopt : NativeHostLight.Adopt := fun _ _ => pure ()) : IO (LightResult config light.opening) :=
  receiveServedWith config transport light bytes none adopt

/-- Private-only route-bound dispatch on the light route. -/
def receiveRouteBoundServed (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (bytes : List UInt8)
    (adopt : NativeHostLight.Adopt := fun _ _ => pure ()) : IO (LightResult config light.opening) := do
  let some (constraint, ingress) := routeBoundCodec.decode bytes
    | return .rejected "noncanonical route-bound dispatch envelope"
  receiveServedWith config transport light ingress (some constraint) adopt

/-- A previously accepted exact call returns its original receipt before any current-law check:
revocation cannot relabel an accepted call as absent. -/
theorem light_historical_receipt_only (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (adopt : NativeHostLight.Adopt)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) (transactionId : Digest)
    (receipt : NativeHostCodec.Receipt)
    (call : ApplicationDispatchLookup.callTransaction ingress = some transactionId)
    (found : ApplicationDispatchLookup.lookupLight (light.opening.reader transport ResourceBirthCodec.rootBytes)
      ingress transactionId = pure (.ok (.historical receipt))) :
    receiveServed config transport light (ApplicationDispatchAdmissionIngress.codec.encode ingress) adopt =
      pure (.historical receipt) := by
  simp only [receiveServed, receiveServedWith, ApplicationDispatchAdmissionIngress.codec.decode_encode]
  split
  · next none => rw [call] at none; cases none
  · next tx exact =>
      rw [call] at exact
      cases Option.some.inj exact
      simp [found]

/-- An occupied/conflicting or unreadable historical identity is never a marker-clearing
refusal, even if current admission would also fail. -/
theorem light_conflicting_lookup_not_clear (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (adopt : NativeHostLight.Adopt)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) (transactionId : Digest)
    (reason : ApplicationDispatchLookup.Error)
    (call : ApplicationDispatchLookup.callTransaction ingress = some transactionId)
    (conflict : ApplicationDispatchLookup.lookupLight (light.opening.reader transport ResourceBirthCodec.rootBytes)
      ingress transactionId = pure (.error reason)) :
    receiveServed config transport light (ApplicationDispatchAdmissionIngress.codec.encode ingress) adopt =
      pure (.rejected "dispatch historical identity unavailable or conflicting") := by
  simp only [receiveServed, receiveServedWith, ApplicationDispatchAdmissionIngress.codec.decode_encode]
  split
  · next none => rw [call] at none; cases none
  · next tx exact =>
      rw [call] at exact
      cases Option.some.inj exact
      simp [conflict]

/-- Even fully signed authority material for a continuity probe or a route probe cannot be
submitted: an absent call with a reserved probe request is refused with its absence, before any
admission or CAS. -/
theorem light_probe_never_submits (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (adopt : NativeHostLight.Adopt)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) (transactionId : Digest)
    (call : ApplicationDispatchLookup.callTransaction ingress = some transactionId)
    (opens : DurableIndex.Opens light.opening.head.indexRoot (DurableIndex.transactionKey transactionId) none)
    (absent : ApplicationDispatchLookup.lookupLight (light.opening.reader transport ResourceBirthCodec.rootBytes)
      ingress transactionId = pure (.ok (.absent opens)))
    (probe : ApplicationStreamContinuity.reservedProbe ingress.dispatch.dispatch.request = true) :
    receiveServed config transport light (ApplicationDispatchAdmissionIngress.codec.encode ingress) adopt =
      pure (.noRecordRefused ⟨transactionId, call, opens⟩) := by
  simp only [receiveServed, receiveServedWith, ApplicationDispatchAdmissionIngress.codec.decode_encode]
  split
  · next none => rw [call] at none; cases none
  · next tx exact =>
      rw [call] at exact
      cases Option.some.inj exact
      simp [absent, probe]

#assert_axioms light_nonwinner_receipt_only
#assert_axioms light_recovered_receipt_only
#assert_axioms light_historical_receipt_only
#assert_axioms light_conflicting_lookup_not_clear
#assert_axioms light_probe_never_submits
#assert_axioms light_mismatched_route_never_submits

end Minidregg.Kernel.ApplicationDispatchReceiver
