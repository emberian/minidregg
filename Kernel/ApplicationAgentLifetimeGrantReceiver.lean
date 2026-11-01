/-
Fresh event27 grant issue on the light opening (`receiveServed`, KN2 2b): its original event22
ticket selected from the Store's history at the grant's issue index and re-admitted at its own
prefix (`NativeHostReplay.selectIssue`), the grant birth and current app delegation admitted on
the light ground of its keys, committed by `DurableServed.receiveServed`. The lower birth/app
checks cannot supply the original event22 ticket by themselves. Receipt-only lookup
(`lookupLight`) reads the transaction's record through the Store's history; the walk's lookup
(`lookupVerified`, the inspection's) selects the exact event27 its walk admitted, including its
initialized cell root.
-/
module

public import Kernel.NativeHost
public import Kernel.NativeHostLight

@[expose] public section

namespace Minidregg.Kernel.ApplicationAgentLifetimeGrantReceiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.ApplicationAgentLifetimeGrantSource
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

def transaction (config : Config) (ingress : Ingress) :
    Minidregg.Theory.TypedAuthorization.Digest :=
  ResourceBirthController.Concrete.sourceIdentity config.profile.compilerProfile
    config.deployment ingress.spec.grant.approval.issuer
    ingress.spec.grant.approval.nonce

/-- A transaction ID occupied by a different original is a conflict, not a
missing grant that may be freshly submitted. -/
def lookupVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress) :
    Option (Except String (NativeHostReplay.PriorLifetimeGrant config)) := do
  let tx := transaction config ingress
  let some _ := verified.opened.durable.image.accepted.find?
      (fun record => record.transactionId == tx)
    | none
  let some original := verified.grants.find?
      (fun prior => prior.record.transactionId == tx)
    | some (.error "agent lifetime grant transaction is not an admitted event27")
  if original.ingress.canonicalBytes.toByteArray ==
      ingress.canonicalBytes.toByteArray then
    some (.ok original)
  else some (.error "agent lifetime grant original ingress differs")

/-! ## The light route -/

/-- The keys a grant's admission reads beyond the state: its transaction id (the walk's lookup
key and the signed birth descriptor's) and the birth's replay marker
(`ResourceBirthReceiver.birthKeys`); a birth that does not decode adds no birth key (its
admission refuses it). -/
def keys (config : Config) (ingress : Ingress) : DurableView.Keys :=
  match ResourceBirthPolicyController.Concrete.decodeLifetimeGrantIngress ingress.birthIngress with
  | some decoded =>
      ⟨[transaction config ingress, decoded.descriptor.transactionId],
        [ResourceBirthReceiver.birthNullifier config.deployment.domain decoded.descriptor.authorityNullifier]⟩
  | none => ⟨[transaction config ingress], []⟩

/-- A grant confirmed on the light route: its original event22 ticket selected from the Store's
history at the grant's issue index and re-admitted at its own prefix, the grant within that
ticket's scope, its birth and app delegation admitted on the light ground at the opening's head,
its transaction verified unrecorded there, and the appended record exactly its intent's. -/
structure LightConfirmed (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes) where
  private mk ::
  ingress : Ingress
  grounded : ServedBasis.Grounded config.deployment opening.head
  issue : NativeHostReplay.IssueSelected config opening.head ingress.spec.grant.source.issueIndex
  event22 : issue.evidence.record.event.codecVersion = 22
  issueReceipt : issue.receipt = ingress.spec.grant.source.issueReceipt
  scope : ingress.spec.grant.matchesIssued issue.evidence.spec ingress.spec.grant.source.issueIndex
    issue.receipt = true
  pins : Minidregg.Theory.ResourceBirth.FactoryPins
  current : ApplicationAgentLifetimeGrantAdmission.Accepted config.profile config pins grounded.ground
    (config.genesisHeight + grounded.ground.height) ingress
  fresh : grounded.ground.recorded (ApplicationAgentLifetimeGrantIntentTemplate.template current).transactionId =
    some none
  kind : DurableReceiverIO.Confirmation
  next : DurableServed.Opening ResourceBirthCodec.rootBytes
  height : next.head.height = opening.head.height + 1
  entry : DurableReceiverIO.Entry
  entryExact : entry.record = DurableCheckpointCodec.recordFrame.encode
    (DurableReceiver.IntentRecord.ofIntent (ApplicationAgentLifetimeGrantIntentTemplate.template current))

/-- **What a light grant confirmation proves**: the appended record is the admitted grant's
intent's, written as the opening's next record; the record verified under the opening's head at
the grant's issue index is the event22 ticket re-admitted at its own prefix, whose receipt is the
one the grant names and whose spec the grant stays within; the grant's transaction id was
verified unrecorded on the light ground it was admitted on. -/
theorem LightConfirmed.exact {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    (confirmed : LightConfirmed config opening) :
    confirmed.entry.record = DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent
          (ApplicationAgentLifetimeGrantIntentTemplate.template confirmed.current)) ∧
      confirmed.next.head.height = opening.head.height + 1 ∧
      (∃ read : DurableHistoryReader.Record opening.head
          (confirmed.ingress.spec.grant.source.issueIndex + 1),
        read.record = confirmed.issue.evidence.record) ∧
      confirmed.issue.evidence.record.event.codecVersion = 22 ∧
      confirmed.issue.receipt = confirmed.ingress.spec.grant.source.issueReceipt ∧
      confirmed.ingress.spec.grant.matchesIssued confirmed.issue.evidence.spec
        confirmed.ingress.spec.grant.source.issueIndex confirmed.issue.receipt = true ∧
      confirmed.grounded.ground.recorded
          (ApplicationAgentLifetimeGrantIntentTemplate.template confirmed.current).transactionId = some none :=
  ⟨confirmed.entryExact, confirmed.height,
    confirmed.issue.read_evidence,
    confirmed.event22, confirmed.issueReceipt, confirmed.scope, confirmed.fresh⟩

def LightConfirmed.intent {config : Config} {opening : DurableServed.Opening ResourceBirthCodec.rootBytes}
    (confirmed : LightConfirmed config opening) : DurableDataIntent.DataIntent ResourceBirthCodec.rootBytes :=
  ApplicationAgentLifetimeGrantIntentTemplate.template confirmed.current

inductive LightResult (config : Config) (opening : DurableServed.Opening ResourceBirthCodec.rootBytes) where
  | confirmed (confirmed : LightConfirmed config opening)
  | historical (receipt : NativeHostCodec.Receipt)
  | rejected (detail : String)
  | transactionConflict
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

/-- **Receipt-only lookup through the Store's history**: the grant's transaction id read by the
Reader; its record's receipt when that record carries exactly this grant's event (the event
carries the whole canonical ingress), a conflict when it carries any other. -/
def lookupLight (config : Config) {store : DurableHistory.StoreIdentity}
    (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store) (ingress : Ingress) :
    IO (Except String (Option (Except String NativeHostCodec.Receipt))) := do
  let tx := transaction config ingress
  match ← reader.byTx tx with
  | .error refusal => return .error refusal.message
  | .ok (.absent _) => return .ok none
  | .ok (.present found) =>
      if found.read.record.event == ApplicationAgentLifetimeGrantSource.event config.deployment.domain ingress then
        return .ok (some (.ok (NativeHost.receiptOfFound tx found)))
      else return .ok (some (.error "agent lifetime grant transaction has a different original"))

/-- **The light grant**: a recorded transaction answers by its receipt (`lookupLight`); otherwise
its original event22 ticket is selected at the grant's issue index and re-admitted at its prefix,
the grant admitted on the light ground of its keys (`keys`) at the opening's head, committed by
`receiveServed`, the readback handed to `adopt`. -/
def receiveServed (config : Config) (transport : DurableReceiverIO.Transport)
    (light : NativeHostLight.Light config) (bytes : List UInt8)
    (adopt : NativeHostLight.Adopt := fun _ _ => pure ()) :
    IO (LightResult config light.opening) := do
  let some ingress := ingressCodec.decode bytes
    | return .rejected "noncanonical agent lifetime grant ingress"
  unless ingress.canonicalBytes.toByteArray == bytes.toByteArray do
    return .rejected "noncanonical agent lifetime grant ingress"
  let reader := light.opening.reader transport ResourceBirthCodec.rootBytes
  match ← lookupLight config reader ingress with
  | .error detail => return .unavailable detail
  | .ok (some (.ok receipt)) => return .historical receipt
  | .ok (some (.error _)) => return .transactionConflict
  | .ok none =>
    let grounded ← match ← light.groundedVia transport (keys config ingress) with
      | .error detail => return .unavailable detail
      | .ok grounded => pure grounded
    let index := ingress.spec.grant.source.issueIndex
    let issue ← match ← NativeHostReplay.selectIssue config reader light.opened.pins
        grounded.ground.height index with
      | .error (.history detail) => return .unavailable s!"agent lifetime grant original event22 issue: history unavailable: {detail}"
      | .error (.refused detail) => return .rejected s!"agent lifetime grant original event22 issue absent: {detail}"
      | .ok issue => pure issue
    if event22 : issue.evidence.record.event.codecVersion = 22 then
      if issueReceipt : issue.receipt = ingress.spec.grant.source.issueReceipt then
        if scope : ingress.spec.grant.matchesIssued issue.evidence.spec index issue.receipt = true then
          match ← ApplicationAgentLifetimeGrantAdmission.admitNative config.profile
              config light.opened.pins config.signature grounded.ground
              (config.genesisHeight + grounded.ground.height) ingress.canonicalBytes with
          | .error _ => return .rejected "agent lifetime grant native admission refused"
          | .ok ⟨decoded, accepted⟩ =>
          if same : decoded = ingress then
            have current : ApplicationAgentLifetimeGrantAdmission.Accepted config.profile config
                light.opened.pins grounded.ground (config.genesisHeight + grounded.ground.height) ingress := by
              cases same
              exact accepted
            match fresh : grounded.ground.recorded
                (ApplicationAgentLifetimeGrantIntentTemplate.template current).transactionId with
            | none => return .rejected "agent lifetime grant transaction identity undeclared"
            | some (some _) => return .transactionConflict
            | some none =>
                match ← DurableServed.receiveServed transport ResourceBirthCodec.rootBytes light.opening
                    (ApplicationAgentLifetimeGrantIntentTemplate.template current) with
                | .appended kind next height entry entryExact _ =>
                    adopt next none
                    return .confirmed ⟨ingress, grounded, issue, event22, issueReceipt, scope,
                      light.opened.pins, current, fresh, kind, next, height, entry, entryExact⟩
                -- Recorded between the lookup and the append: the lookup answers on retry.
                | .replayed _ => return .contention
                | .rejected _ => return .rejected "agent lifetime grant durable refusal"
                | .contention => return .contention
                | .unavailable detail => return .unavailable detail
                | .uncertain detail => return .uncertain detail
          else return .rejected "agent lifetime grant ingress changed at native admission"
        else return .rejected "agent lifetime grant exceeds original ticket scope"
      else return .rejected "agent lifetime grant original receipt differs"
    else return .rejected "agent lifetime grant original ticket was not event22"

end Minidregg.Kernel.ApplicationAgentLifetimeGrantReceiver
