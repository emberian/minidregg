/-
One event28 CAS and receipt-only recovery on the light opening (KN2 2b): the original event22
ticket selected from the Store's history at the enrollment's issue index and re-admitted at its
own prefix (`NativeHostReplay.selectIssue`), the joint enrollment and its three signed reads
admitted on the light ground of its keys, committed by `DurableServed.receiveServed`.
-/
module

public import Kernel.NativeHost
public import Kernel.NativeHostLight

@[expose] public section

namespace Minidregg.Kernel.ApplicationGrainSessionEnrollmentReceiver

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationGrainSessionEnrollmentSource

set_option autoImplicit false

private def transaction (config : Config) (ingress : Ingress) :
    Option Minidregg.Theory.TypedAuthorization.Digest := do
  let (domain, semantics, signed) ←
    DeclaredResourceController.decodeSignedBytes ingress.signedBytes
  if domain != config.deployment.domain || semantics != config.profile.semantics then none else
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  some (DeclaredResourceController.transactionId domain semantics command)

/-- **Receipt-only lookup through the Store's history.** A missing transaction may be submitted
once. An occupied transaction whose record carries a different event is a conflict, never a
retry signal; one carrying exactly this enrollment's event answers by its receipt. -/
def lookupLight (config : Config) {store : DurableHistory.StoreIdentity}
    (reader : DurableHistoryReader.Reader rootBytes store) (ingress : Ingress) :
    IO (Except String (Option (Except String Receipt))) := do
  let some tx := transaction config ingress
    | return .ok (some (.error "noncanonical enrollment signed command"))
  match ← reader.byTx tx with
  | .error refusal => return .error refusal.message
  | .ok (.absent _) => return .ok none
  | .ok (.present found) =>
      if found.read.record.event == ApplicationGrainSessionEnrollmentSource.event config.deployment.domain ingress then
        return .ok (some (.ok (NativeHost.receiptOfFound tx found)))
      else return .ok (some (.error "enrollment transaction has a different original"))

/-- An enrollment confirmed on the light route: its original event22 ticket selected from the
Store's history at the ingress's issue index and re-admitted at its own prefix, with the receipt
and ticket resource the ingress names; the joint enrollment and its three signed reads admitted on
the light ground at the opening's head; its transaction verified unrecorded there; and the
appended record exactly its intent's. -/
structure LightConfirmed (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes) where
  private mk ::
  ingress : Ingress
  grounded : ServedBasis.Grounded config.deployment opening.head
  issue : NativeHostReplay.IssueSelected config opening.head ingress.request.issueIndex
  event22 : issue.evidence.record.event.codecVersion = 22
  issueReceipt : issue.receipt = ingress.issueReceipt
  ticketResource : issue.evidence.spec.ticket.resource = ingress.request.ticketResource
  checked : ApplicationGrainSessionEnrollmentAdmission.Checked config grounded.ground ingress
    issue.evidence.spec issue.receipt
  fresh : grounded.ground.recorded (ApplicationGrainSessionEnrollmentIntent.intent checked).transactionId =
    some none
  kind : DurableReceiverIO.Confirmation
  next : DurableServed.Opening ResourceBirthCodec.rootBytes
  height : next.head.height = opening.head.height + 1
  entry : DurableReceiverIO.Entry
  entryExact : entry.record = DurableCheckpointCodec.recordFrame.encode
    (DurableReceiver.IntentRecord.ofIntent (ApplicationGrainSessionEnrollmentIntent.intent checked))

def LightConfirmed.intent {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    (confirmed : LightConfirmed config opening) : DurableDataIntent.DataIntent rootBytes :=
  ApplicationGrainSessionEnrollmentIntent.intent confirmed.checked

/-- **What a light enrollment confirmation proves**: the appended record is the admitted
enrollment's intent's, written as the opening's next record; the record verified under the
opening's head at the ingress's issue index is the event22 ticket re-admitted at its own prefix,
with the receipt the ingress names; the enrollment's three read guards expect the light ground's
current roots; its transaction id was verified unrecorded on that ground. -/
theorem LightConfirmed.exact {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    (confirmed : LightConfirmed config opening) :
    confirmed.entry.record = DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent confirmed.intent) ∧
      confirmed.next.head.height = opening.head.height + 1 ∧
      (∃ read : DurableHistoryReader.Record opening.head (confirmed.ingress.request.issueIndex + 1),
        read.record = confirmed.issue.evidence.record) ∧
      confirmed.issue.evidence.record.event.codecVersion = 22 ∧
      confirmed.issue.receipt = confirmed.ingress.issueReceipt ∧
      (∀ guard ∈ ApplicationGrainSessionEnrollmentIntent.readGuards confirmed.checked,
        guard.expectedRoot = confirmed.grounded.ground.cells.model.roots guard.cellId) ∧
      confirmed.grounded.ground.recorded confirmed.intent.transactionId = some none :=
  ⟨confirmed.entryExact, confirmed.height,
    confirmed.issue.read_evidence,
    confirmed.event22, confirmed.issueReceipt,
    ApplicationGrainSessionEnrollmentIntent.readGuards_current confirmed.checked, confirmed.fresh⟩

inductive LightResult (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes) where
  | confirmed (confirmed : LightConfirmed config opening)
  | historical (receipt : Receipt)
  | rejected (detail : String)
  | transactionConflict
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

/-- **The light enrollment**: a recorded transaction answers by its receipt (`lookupLight`);
otherwise its original event22 ticket is selected at the issue index and re-admitted at its
prefix, the enrollment admitted on the light ground of its keys
(`ApplicationGrainSessionEnrollmentAdmission.keys`) at the opening's head, committed by
`receiveServed`, the readback handed to `adopt`. -/
def receiveServed (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (bytes : List UInt8)
    (adopt : NativeHostLight.Adopt := fun _ _ => pure ()) :
    IO (LightResult config light.opening) := do
  let some ingress := ingressCodec.decode bytes
    | return .rejected "noncanonical enrollment ingress"
  unless ingress.canonicalBytes.toByteArray == bytes.toByteArray do
    return .rejected "noncanonical enrollment ingress"
  let reader := light.opening.reader transport ResourceBirthCodec.rootBytes
  match ← lookupLight config reader ingress with
  | .error detail => return .unavailable detail
  | .ok (some (.ok receipt)) => return .historical receipt
  | .ok (some (.error _)) => return .transactionConflict
  | .ok none =>
    let grounded ← match ← light.groundedVia transport
        (ApplicationGrainSessionEnrollmentAdmission.keys config ingress) with
      | .error detail => return .unavailable detail
      | .ok grounded => pure grounded
    let issue ← match ← NativeHostReplay.selectIssue config reader light.opened.pins
        grounded.ground.height ingress.request.issueIndex with
      | .error (.history detail) => return .unavailable s!"session enrollment original event22 ticket: history unavailable: {detail}"
      | .error (.refused detail) => return .rejected s!"session enrollment original event22 ticket absent: {detail}"
      | .ok issue => pure issue
    if event22 : issue.evidence.record.event.codecVersion = 22 then
      if issueReceipt : issue.receipt = ingress.issueReceipt then
        if ticketResource : issue.evidence.spec.ticket.resource = ingress.request.ticketResource then
          match ← ApplicationGrainSessionEnrollmentAdmission.admitAt config grounded.ground ingress
              issue.evidence.spec issue.receipt with
          | .error detail => return .rejected detail
          | .ok checked =>
          match fresh : grounded.ground.recorded
              (ApplicationGrainSessionEnrollmentIntent.intent checked).transactionId with
          | none => return .rejected "enrollment transaction identity undeclared"
          | some (some _) => return .transactionConflict
          | some none =>
              match ← DurableServed.receiveServed transport ResourceBirthCodec.rootBytes light.opening
                  (ApplicationGrainSessionEnrollmentIntent.intent checked) with
              | .appended kind next height entry entryExact _ =>
                  adopt next none
                  return .confirmed ⟨ingress, grounded, issue, event22, issueReceipt, ticketResource,
                    checked, fresh, kind, next, height, entry, entryExact⟩
              -- Recorded between the lookup and the append: the lookup answers on retry.
              | .replayed _ => return .contention
              | .rejected _ => return .rejected "durable enrollment refused"
              | .contention => return .contention
              | .unavailable detail => return .unavailable detail
              | .uncertain detail => return .uncertain detail
        else return .rejected "session enrollment original ticket resource differs"
      else return .rejected "session enrollment original ticket receipt differs"
    else return .rejected "session enrollment original ticket was not event22"

end Minidregg.Kernel.ApplicationGrainSessionEnrollmentReceiver
