/-
# Kernel.ObjectiveActivityReceiver — the kernel activity as signed native commands

Every turn of the kernel activity (`Kernel.ObjectiveActivity`) is one signed
native command (`Command`: subject, nonce, the pinned authority root, and one
`Turn`), admitted by the Host the way every kernel family is admitted
(the clock tick, job money, certify): the signer's Ed25519 signature over the
exact request header (`CredentialSignatureAdmission.verifyNative`, the
subject's current enrolled key), its single-use marker as the intent's
durable nullifier, the authority cell as a read guard, the durable receiving
loop (`DurableReceiverIO.receiveLoaded`: CAS on every write, claims, the tail
bound), and the replay walk (`NativeHostReplay`) re-admitting the retained
ingress at its original height on every reopen and audit.

The turn the kernel decides is its intent, under this receiver's seal:
`Decided.intent` is literally `Birth.intent` / `Delivery.intent` / ... of
`Kernel.ObjectiveActivity` with the sealing `seal`, so every resume-contract
theorem stated there for every sealing holds of the intent this receiver commits
(`native_delivery_consumes_once`, `native_delivery_fields_bind_checkpoint`).

**Objects** (ROOT ruling OBJECT AUTHORITY). A cell is an object to the kernel
only with a record (`Kernel.ObjectRecord`: the pinned package, the law that
judges every declared-state write, the upgrade policy, the payer), installed by
a `create` turn. A creation, a birth and an invocation name the object
(a native resource cell) and a capability on it; they are admitted only when
that capability is admissible for a mutation of the object by the signer
(`objectHolder`: the authority layer's own `capabilityAdmissibleCheck`: holder,
scope, window, the object's law epoch, issuer, revocation), else refused
`notObjectHolder` (`create_requires_object_holder`, `birth_requires_object_holder`). What may be born and written is the
kernel's: a birth on a cell without a record is refused `notAnObject`, under
another package than the pinned one `pinMismatch` (`native_birth_on_pinned_object`),
and a write the object's law refuses `objectWrite` with the failing clause.
A turn that spends credit, or names a payer, names a Book account and a
capability on it and is admitted only for the account's owner (`accountHolder`:
the owner grant and an admissible `transfer`), else refused `notAccountOwner`.
Exhaustion and abandonment are anyone's (the kernel decides whether the await
exhausted or is past its deadline plus grace); an added envelope needs the
account owner.

**Protected coordinates.** Every activity cell is a registry cell of role
`objectiveActivity` at its coordinate; no birth may install the role
(`UserShape`), no other receiver selects it, and the cells this receiver writes
are exactly activity cells and the Book (`intent_writes_activity_or_book`).

**The signature binds the outcome.** The signed request's effect digest commits
to the command bytes and to the digest of the decided turn's posts (`Declaration`),
computed by the Host at planning: a turn whose outcome changed between the
signing plan and the submission no longer matches the signed header.

**Configuration** (`Kernel.ObjectiveKernelConfig.configOf`). The kernel's
envelope ceilings and tariff are the deployment's Objective policy (the
`objectiveMethod` route binding the genesis pins: `maximum`, `tariff`,
`sourceBytes`), and an operator who disabled Core4 (`objective-core4`) disables
activities with it. Fees are in the deployment's creation-tariff asset, paid to
its collector.
-/
import Kernel.CapabilityRevocationController
import Kernel.ResourceBirthController
import Kernel.ObjectiveActivity
import Kernel.ActivitySeatEnd
import Kernel.ObjectiveAdmittedTurn
import Kernel.ObjectiveKernelConfig
import Kernel.ObjectiveBendNativeAdmission
import Kernel.PayAssignmentReceiver

namespace Minidregg.Kernel.ObjectiveActivityReceiver

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Kernel.ObjectiveActivity (Config Publication Creation Birth Resolution Delivery TopUp
  Exhaustion Abandonment CreateRequest BirthRequest ResolveRequest DeliverRequest TopUpRequest
  ExhaustRequest AbandonRequest Answer)
open Minidregg.Kernel.ObjectiveKernelConfig (Ambient configOf)
open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity capacityStream)
open Minidregg.Kernel.ObjectiveTariff (zeroCapacity)

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot

/-! ## Command and ingress -/

/-- A slot decision as signed: a reply (data bytes), a refusal, unknown, broken. -/
inductive AnswerWire where
  | reply (value : List UInt8)
  | refused (reason : String)
  | unknown
  | broken (reason : String)
  deriving DecidableEq, Repr

def answerStream : StreamCodec AnswerWire :=
  StreamCodec.xmap (StreamCodec.sum bytesStream (StreamCodec.sum stringStream
      (StreamCodec.sum StreamCodec.nat stringStream)))
    (fun answer => match answer with
      | .reply value => .inl value
      | .refused reason => .inr (.inl reason)
      | .unknown => .inr (.inr (.inl 0))
      | .broken reason => .inr (.inr (.inr reason)))
    (fun wire => match wire with
      | .inl value => .reply value
      | .inr (.inl reason) => .refused reason
      | .inr (.inr (.inl _)) => .unknown
      | .inr (.inr (.inr reason)) => .broken reason)
    (by intro answer; cases answer <;> rfl)

inductive Turn where
  /-- Publish an activity package: the artifact bytes WITH the source package
  bytes the front end replays to that artifact's core, funded by `payer`
  (`ObjectiveActivity.Stored`). -/
  | publish (artifact package : List UInt8) (payer : Nat) (payerCapability : CapabilityId)
  /-- Make `object` (a native resource cell) an object to the kernel: install its
  record pinning the published package `pin`, its declared state typed at `stateType`,
  judged by `law`, re-pinnable under `upgrade`, funded by `payer`
  (`ObjectiveActivity.create`), and optionally install its initial declared state `seed`
  (data bytes), judged by `law` alone and typed at `stateType`. Only a holder of a
  capability on the object, naming a payer account it owns. -/
  | create (object : Nat) (objectCapability : CapabilityId) (pin : Digest)
      (stateType : Minidregg.Theory.ObjectiveBendTypes.Ty) (law : Minidregg.Pred.Pred)
      (upgrade : ObjectRecord.UpgradePolicy) (seed : Option (List UInt8)) (payer : Nat)
      (payerCapability : CapabilityId)
  /-- Birth an activity of `pin` on `object` with `input` (data bytes), paid
  from `account`, with the declared envelopes (the birth's own, each resume's
  and the timeout's) and the purse deposit. The kernel refuses an object
  without a record and a pin other than the object's. -/
  | birth (object : Nat) (objectCapability : CapabilityId) (account : Nat) (accountCapability : CapabilityId)
      (pin : Digest) (input : List UInt8) (envelope resume timeout : Capacity) (deposit : Nat)
  /-- Decide an answer slot. -/
  | resolve (slot : Digest) (answer : AnswerWire)
  /-- End the await `await` of the activity at `record`; an `extra` envelope
  (added to the escrowed one) is paid from `account` (zero and 0 when none). -/
  | deliver (record : Digest) (await : Digest) (extra : Capacity) (account : Nat)
      (accountCapability : CapabilityId)
  /-- Fund an activity's purse from `account`. -/
  | topUp (record : Digest) (account : Nat) (accountCapability : CapabilityId) (amount : Nat)
  /-- Commit an exhausted attempt to end the await `await` of the activity at
  `record`: the attempt is paid (its declared envelope; `extra` from
  `account`) and the activity stays at its yield. -/
  | exhaust (record : Digest) (await : Digest) (extra : Capacity) (account : Nat)
      (accountCapability : CapabilityId)
  /-- Abandon the await `await` of the activity at `record` once it is past its
  deadline plus the deployment's grace: reclaim the record and its slot and
  return the purse. Anyone may. -/
  | abandon (record : Digest) (await : Digest)
  /-- Call `method` of `object` with `args` (data bytes): the call tree runs in
  this turn (`Kernel.ObjectiveCall`), every callee on its own pinned package,
  within the one declared `envelope`, whose public price `account` pays.
  `grants` lend the signer's authority to named nested frames. Every message the
  tree sends is delivered under `postage`, whose price `account` escrows per
  send. Only a holder of a capability on `object`, spending an account it owns. -/
  | invoke (object : Nat) (objectCapability : CapabilityId) (method : String) (args : List UInt8)
      (grants : List ObjectiveCall.Grant) (envelope postage : Capacity) (account : Nat)
      (accountCapability : CapabilityId)
  /-- Deliver the head `message` of the inbox (sender, target)
  (`Kernel.ObjectiveSend`): anyone may; paid from the inbox's purse. -/
  | deliverMessage (sender target : Nat) (message : Digest)
  /-- ADOPT an upgrade of `object` (`ObjectiveActivityUpgrade.adopt`): the next package `pin`, its
  state type, its migration (a declaration of `pin`, or none for the identity), the old fields it
  drops, the next law and policy, the activities to re-birth, the migration's declared envelope
  (whose price `account` pays) and the drain patience. Only a holder of a capability on the
  object, spending an account it owns; the object's policy then judges the request. -/
  | adopt (object : Nat) (objectCapability : CapabilityId) (pin : Digest)
      (stateType : Minidregg.Theory.ObjectiveBendTypes.Ty) (migration : Option String) (dropped : List String)
      (law : Minidregg.Pred.Pred) (upgrade : ObjectRecord.UpgradePolicy) (rebirth : List Digest)
      (envelope : Capacity) (patience : Nat) (account : Nat) (accountCapability : CapabilityId)
  /-- MIGRATE a drained object (anyone, paying the migration's price from `account`). -/
  | migrate (object : Nat) (account : Nat) (accountCapability : CapabilityId)
  /-- Abort the await `await` of an old activity at `record` after the drain deadline: it is
  resumed with `upgraded` for one ending segment (anyone; `extra` from `account`). -/
  | abortDrained (record : Digest) (await : Digest) (extra : Capacity) (account : Nat)
      (accountCapability : CapabilityId)
  /-- Re-birth the activity at `record` (left on the old package by a migration) on the
  object's package from its stored input (anyone; paid from its own purse). -/
  | rebirth (record : Digest) (await : Digest) (envelope : Capacity)
  deriving DecidableEq, Repr

abbrev CreateWire :=
  Nat × CapabilityId × Digest × Minidregg.Theory.ObjectiveBendTypes.Ty × Minidregg.Pred.Pred ×
    ObjectRecord.UpgradePolicy × Option (List UInt8) × Nat × CapabilityId
abbrev PublishWire := List UInt8 × List UInt8 × Nat × CapabilityId
abbrev BirthWire :=
  Nat × CapabilityId × Nat × CapabilityId × Digest × List UInt8 × Capacity × Capacity × Capacity × Nat
abbrev EndWire := Digest × Digest × Capacity × Nat × CapabilityId
abbrev InvokeWire :=
  Nat × CapabilityId × String × List UInt8 × List ObjectiveCall.Grant × Capacity × Capacity × Nat × CapabilityId
abbrev AdoptWire :=
  Nat × CapabilityId × Digest × Minidregg.Theory.ObjectiveBendTypes.Ty × Option String × List String ×
    Minidregg.Pred.Pred × ObjectRecord.UpgradePolicy × List Digest × Capacity × Nat × Nat × CapabilityId

abbrev TurnWire :=
  Sum PublishWire (Sum CreateWire (Sum BirthWire (Sum (Digest × AnswerWire) (Sum EndWire
    (Sum (Digest × Nat × CapabilityId × Nat)
      (Sum EndWire (Sum (Digest × Digest) (Sum InvokeWire (Sum (Nat × Nat × Digest)
        (Sum AdoptWire (Sum (Nat × Nat × CapabilityId) (Sum EndWire (Digest × Digest × Capacity)))))))))))))

def Turn.toWire : Turn → TurnWire
  | .publish artifact package p pc => .inl (artifact, package, p, pc)
  | .create o oc pin st law upgrade seed p pc => .inr (.inl (o, oc, pin, st, law, upgrade, seed, p, pc))
  | .birth o oc a ac pin input t r tt d => .inr (.inr (.inl (o, oc, a, ac, pin, input, t, r, tt, d)))
  | .resolve slot answer => .inr (.inr (.inr (.inl (slot, answer))))
  | .deliver record await extra account cap => .inr (.inr (.inr (.inr (.inl (record, await, extra, account, cap)))))
  | .topUp record account cap amount => .inr (.inr (.inr (.inr (.inr (.inl (record, account, cap, amount))))))
  | .exhaust record await extra account cap =>
      .inr (.inr (.inr (.inr (.inr (.inr (.inl (record, await, extra, account, cap)))))))
  | .abandon record await => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (record, await))))))))
  | .invoke o oc method args grants envelope postage a ac =>
      .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (o, oc, method, args, grants, envelope, postage, a, ac)))))))))
  | .deliverMessage sender target message =>
      .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (sender, target, message))))))))))
  | .adopt o oc pin st mig dropped law upgrade chosen envelope patience a ac =>
      .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (o, oc, pin, st, mig, dropped, law, upgrade, chosen, envelope, patience, a, ac)))))))))))
  | .migrate o a ac => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (o, a, ac))))))))))))
  | .abortDrained record await extra a ac => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (record, await, extra, a, ac)))))))))))))
  | .rebirth record await envelope => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ((record, await, envelope))))))))))))))

def Turn.ofWire : TurnWire → Turn
  | .inl (artifact, package, p, pc) => .publish artifact package p pc
  | .inr (.inl (o, oc, pin, st, law, upgrade, seed, p, pc)) => .create o oc pin st law upgrade seed p pc
  | .inr (.inr (.inl (o, oc, a, ac, pin, input, t, r, tt, d))) => .birth o oc a ac pin input t r tt d
  | .inr (.inr (.inr (.inl (slot, answer)))) => .resolve slot answer
  | .inr (.inr (.inr (.inr (.inl (record, await, extra, account, cap))))) => .deliver record await extra account cap
  | .inr (.inr (.inr (.inr (.inr (.inl (record, account, cap, amount)))))) => .topUp record account cap amount
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (record, await, extra, account, cap))))))) =>
      .exhaust record await extra account cap
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (record, await)))))))) => .abandon record await
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (o, oc, method, args, grants, envelope, postage, a, ac))))))))) =>
      .invoke o oc method args grants envelope postage a ac
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (sender, target, message)))))))))) =>
      .deliverMessage sender target message
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (o, oc, pin, st, mig, dropped, law, upgrade, chosen, envelope, patience, a, ac))))))))))) =>
      .adopt o oc pin st mig dropped law upgrade chosen envelope patience a ac
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (o, a, ac)))))))))))) => .migrate o a ac
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (record, await, extra, a, ac))))))))))))) => .abortDrained record await extra a ac
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ((record, await, envelope)))))))))))))) => .rebirth record await envelope

def createStream : StreamCodec CreateWire :=
  StreamCodec.product StreamCodec.nat (StreamCodec.product capabilityIdStream
    (StreamCodec.product digestStream (StreamCodec.product ObjectStateType.tyStream
      (StreamCodec.product LawLeaf.predStream
      (StreamCodec.product ObjectRecord.upgradeStream (StreamCodec.product (StreamCodec.option bytesStream)
        (StreamCodec.product StreamCodec.nat capabilityIdStream)))))))

def publishStream : StreamCodec PublishWire :=
  StreamCodec.product bytesStream (StreamCodec.product bytesStream
    (StreamCodec.product StreamCodec.nat capabilityIdStream))

def birthStream : StreamCodec BirthWire :=
  StreamCodec.product StreamCodec.nat (StreamCodec.product capabilityIdStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product capabilityIdStream
      (StreamCodec.product digestStream (StreamCodec.product bytesStream
        (StreamCodec.product capacityStream (StreamCodec.product capacityStream
          (StreamCodec.product capacityStream StreamCodec.nat))))))))

def endStream : StreamCodec EndWire :=
  StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product capacityStream (StreamCodec.product StreamCodec.nat capabilityIdStream)))

def invokeStream : StreamCodec InvokeWire :=
  StreamCodec.product StreamCodec.nat (StreamCodec.product capabilityIdStream
    (StreamCodec.product stringStream (StreamCodec.product bytesStream
      (StreamCodec.product (StreamCodec.list ObjectiveCall.grantStream) (StreamCodec.product capacityStream
        (StreamCodec.product capacityStream (StreamCodec.product StreamCodec.nat capabilityIdStream)))))))

def adoptStream : StreamCodec AdoptWire :=
  StreamCodec.product StreamCodec.nat (StreamCodec.product capabilityIdStream
    (StreamCodec.product digestStream (StreamCodec.product ObjectStateType.tyStream
      (StreamCodec.product (StreamCodec.option stringStream) (StreamCodec.product (StreamCodec.list stringStream)
        (StreamCodec.product LawLeaf.predStream (StreamCodec.product ObjectRecord.upgradeStream
          (StreamCodec.product (StreamCodec.list digestStream) (StreamCodec.product capacityStream
            (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat capabilityIdStream)))))))))))

def turnStream : StreamCodec Turn :=
  StreamCodec.xmap
    (StreamCodec.sum publishStream (StreamCodec.sum createStream (StreamCodec.sum birthStream
      (StreamCodec.sum (StreamCodec.product digestStream answerStream) (StreamCodec.sum endStream
        (StreamCodec.sum
          (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat
            (StreamCodec.product capabilityIdStream StreamCodec.nat)))
          (StreamCodec.sum endStream (StreamCodec.sum (StreamCodec.product digestStream digestStream)
            (StreamCodec.sum invokeStream
              (StreamCodec.sum (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat digestStream))
                (StreamCodec.sum adoptStream
                  (StreamCodec.sum (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
                      capabilityIdStream))
                    (StreamCodec.sum endStream
                      (StreamCodec.product digestStream (StreamCodec.product digestStream capacityStream)))))))))))))))
    Turn.toWire Turn.ofWire (by intro turn; cases turn <;> rfl)

structure Command where
  subject : SubjectId
  nonce : Nat
  expectedAuthorityRoot : Digest
  turn : Turn
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream turnStream)))
    (fun c => (c.subject, c.nonce, c.expectedAuthorityRoot, c.turn))
    (fun (subject, nonce, root, turn) => ⟨subject, nonce, root, turn⟩)
    (by intro c; cases c; rfl)

/-- v8: an `invoke`'s grants are v2 (`ObjectiveCall.grantStream`: code, arguments bound, caller);
v7: envelopes carry the extraction tick lane (`Capacity.extractTicks`); v6: the upgrade turns
(`adopt`, `migrate`, `abortDrained`, `rebirth`) join the sum, and `create` declares the object's
state type (`ObjectStateType.tyStream`); v5: `create` carries an optional initial declared state,
and the turn sum has no `writeState`; v7 (and older) commands refuse to decode. -/
def commandFrame : List UInt8 := "DREGG/OBJECTIVE/ACTIVITY/COMMAND/v8".toUTF8.toList

def commandCodec : LawfulCodec Command := ObjectiveActivityWire.framed commandFrame commandStream

theorem command_roundtrip (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

theorem command_canonical {bytes : List UInt8} {command : Command}
    (accepted : commandCodec.decode bytes = some command) : commandCodec.encode command = bytes :=
  ObjectiveActivityWire.framed_canonical accepted

structure Ingress where
  commandBytes : List UInt8
  envelope : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun ingress => (ingress.commandBytes, ingress.envelope))
    (fun (command, envelope) => ⟨command, envelope⟩)
    (by intro ingress; cases ingress; rfl)

def ingressFrame : List UInt8 := "DREGG/OBJECTIVE/ACTIVITY/SIGNED/v1".toUTF8.toList

def ingressCodec : LawfulCodec Ingress := ObjectiveActivityWire.framed ingressFrame ingressStream

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  command : Command
  canonical : commandCodec.encode command = ingress.commandBytes
  envelope : CredentialSignedEnvelopeController.SignedEnvelope
  envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.envelope =
    some envelope

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  let ingress ← ingressCodec.decode bytes
  match commandExact : commandCodec.decode ingress.commandBytes with
  | none => none
  | some command =>
    match envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.envelope with
    | none => none
    | some envelope => some ⟨ingress, command, command_canonical commandExact, envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE.ACTIVITY.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream StreamCodec.nat))).encode
      (domain, semantics, command.subject, command.nonce))).digest.value

/-! ## The kernel turn a command decides -/

def answerOf (wire : AnswerWire) : Except ObjectiveActivity.Refusal Answer :=
  match wire with
  | .reply bytes => match decodeDataBytes bytes with
    | some value => .ok (.reply value)
    | none => .error (.responseType "reply")
  | .refused reason => .ok (.refused reason)
  | .unknown => .ok .unknown
  | .broken reason => .ok (.broken reason)

def birthRequest (command : Command) (object : Nat) (account : Nat) (pin : Digest) (input : Data)
    (envelope resume timeout : Capacity) (deposit : Nat) : BirthRequest :=
  ⟨command.subject, ⟨object⟩, pin, input, command.nonce, envelope, resume, timeout, account, deposit, none⟩

def createRequest (command : Command) (object : Nat) (pin : Digest) (stateType : Minidregg.Theory.ObjectiveBendTypes.Ty)
    (law : Minidregg.Pred.Pred) (upgrade : ObjectRecord.UpgradePolicy) (seed : Option Data) (payer : Nat) :
    CreateRequest :=
  ⟨command.subject, ⟨object⟩, pin, stateType, law, upgrade, seed, payer⟩

/-- A seed's data bytes decode, or the command is undecodable (`none`: no seed, which is fine). -/
def decodeSeed : Option (List UInt8) → Option (Option Data)
  | none => some none
  | some bytes => (decodeDataBytes bytes).map some

def invokeRequest (command : Command) (object : Nat) (method : String) (args : Data)
    (grants : List ObjectiveCall.Grant) (envelope postage : Capacity) (account : Nat) : ObjectiveCall.InvokeRequest :=
  ⟨command.subject, ⟨object⟩, method, args, grants, envelope, account, command.nonce, postage⟩

def messageRequest (command : Command) (sender target : Nat) (message : Digest) : ObjectiveSend.MessageRequest :=
  ⟨command.subject, sender, target, message⟩

def adoptRequest (command : Command) (object : Nat) (pin : Digest) (stateType : Minidregg.Theory.ObjectiveBendTypes.Ty)
    (migration : Option String) (dropped : List String) (law : Minidregg.Pred.Pred)
    (upgrade : ObjectRecord.UpgradePolicy) (rebirth : List Digest) (envelope : Capacity) (patience account : Nat) :
    ObjectiveActivity.AdoptRequest :=
  ⟨command.subject, ⟨object⟩, pin, stateType, migration, dropped, law, upgrade, rebirth, envelope, patience, account,
    command.nonce⟩

def migrateRequest (command : Command) (object account : Nat) : ObjectiveActivity.MigrateRequest :=
  ⟨command.subject, ⟨object⟩, account, command.nonce⟩

/-- The kernel turn a command decided: one `ObjectiveActivity.AdmittedTurn`
(the command fixes which admission function ran). -/
abbrev Decided {rootBytes : List UInt8 → Digest} (config : Config) (snapshot : DataSnapshot rootBytes)
    (height : Nat) (_command : Command) : Type :=
  ObjectiveActivity.AdmittedTurn config snapshot height

/-- The transaction a command's turn commits under: the kernel's own ids,
computable from the command alone (so a retry finds its record by them). -/
def transactionOf (command : Command) : Option TransactionId :=
  match command.turn with
  | .publish artifact _ _ _ =>
      (ObjectiveBendSourceArtifact.decode artifact).map fun a =>
        ObjectiveActivity.publishTransaction (ObjectiveBendSourceArtifact.identity a)
  | .create object _ pin stateType law upgrade seed payer _ =>
      (decodeSeed seed).map fun data =>
        ObjectiveActivity.createTransaction (createRequest command object pin stateType law upgrade data payer)
  | .birth object _ account _ pin input envelope resume timeout deposit =>
      (decodeDataBytes input).map fun value =>
        ObjectiveActivity.birthTransaction
          (birthRequest command object account pin value envelope resume timeout deposit)
  | .resolve slot _ => some (ObjectiveActivity.resolveTransaction slot)
  | .deliver _ await _ _ _ => some (ObjectiveActivity.deliveryTransaction await)
  | .topUp record account _ amount =>
      some (ObjectiveActivity.topUpTransaction ⟨command.subject, record, account, amount, command.nonce⟩)
  | .exhaust record await extra account _ =>
      some (ObjectiveActivity.exhaustTransaction await ⟨command.subject, record, extra, account, command.nonce⟩)
  | .abandon _ await => some (ObjectiveActivity.abandonTransaction await)
  | .invoke object _ method args grants envelope postage account _ =>
      (decodeDataBytes args).map fun value =>
        ObjectiveCall.invokeTransaction (invokeRequest command object method value grants envelope postage account)
  | .deliverMessage _ _ message => some (ObjectiveSend.messageTransaction message)
  | .adopt object _ pin stateType migration dropped law upgrade chosen envelope patience account _ =>
      some (ObjectiveActivity.adoptTransaction
        (adoptRequest command object pin stateType migration dropped law upgrade chosen envelope patience account))
  | .migrate object account _ => some (ObjectiveActivity.migrateTransaction (migrateRequest command object account))
  | .abortDrained _ await _ _ _ => some (ObjectiveActivity.abortTransaction await)
  | .rebirth _ await _ => some (ObjectiveActivity.rebirthTransaction await)

/-- Refusals of this receiver: the kernel's, the authority's, the ingress's. -/
inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | staleAuthority
  | replayedMarker | physicalPreparation | inputUndecodable
  | kernel (reason : ObjectiveActivity.Refusal)
  /-- The ending activity's held seats could not be closed (`ActivitySeatEnd.join`). -/
  | seats (reason : SeatStore.Refusal)
  /-- The call tree of an `invoke` was refused (re-entry, a law, a grant, a fault). -/
  | call (reason : ObjectiveCall.CallRefusal)
  /-- A message delivery was refused (no inbox, an empty or moved head, its reply slot). -/
  | message (reason : ObjectiveSend.MessageRefusal)
  /-- The command's await is not the one the record awaits now. -/
  | staleAwait
  /-- The signer holds no capability admissible for mutating the object. -/
  | notObjectHolder
  /-- The signer does not own the Book account the turn spends or names as payer. -/
  | notAccountOwner
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving Repr

def kernel {α : Type} : Except ObjectiveActivity.Refusal α → Except Reject α
  | .ok value => .ok value
  | .error reason => .error (.kernel reason)

def decideTurn {rootBytes : List UInt8 → Digest} (config : Config) (snapshot : DataSnapshot rootBytes)
    (height : Nat) (command : Command) : Except Reject (Decided config snapshot height command) :=
  match command.turn with
  | .publish artifact package payer _ => do
      let stored : ObjectiveActivity.Stored := ⟨artifact, package, payer⟩
      pure (.publish stored (← kernel (ObjectiveActivity.publish config snapshot stored)))
  | .create object _ pin stateType law upgrade seed payer _ => do
      let some data := decodeSeed seed | throw .inputUndecodable
      let request := createRequest command object pin stateType law upgrade data payer
      pure (.create request (← kernel (ObjectiveActivity.create config snapshot height request)))
  | .birth object _ account _ pin input envelope resume timeout deposit => do
      let some value := decodeDataBytes input | throw .inputUndecodable
      let request := birthRequest command object account pin value envelope resume timeout deposit
      pure (.birth request rfl (← kernel (ObjectiveActivity.birth config snapshot height request)))
  | .resolve slot wire => do
      let answer ← kernel (answerOf wire)
      let request : ResolveRequest := ⟨command.subject, slot, answer⟩
      pure (.resolve request (← kernel (ObjectiveActivity.resolve config snapshot height request)))
  | .deliver record await extra account _ => do
      let request : DeliverRequest := ⟨command.subject, record, extra, account⟩
      let delivery ← kernel (ObjectiveActivity.deliver config snapshot height request)
      if delivery.await.id ≠ await then throw .staleAwait
      pure (.deliver request delivery)
  | .topUp record account _ amount => do
      let request : TopUpRequest := ⟨command.subject, record, account, amount, command.nonce⟩
      pure (.topUp request (← kernel (ObjectiveActivity.topUp config snapshot request)))
  | .exhaust record await extra account _ => do
      let request : ExhaustRequest := ⟨command.subject, record, extra, account, command.nonce⟩
      let exhausted ← kernel (ObjectiveActivity.exhaust config snapshot height request)
      if exhausted.await.id ≠ await then throw .staleAwait
      pure (.exhaust request exhausted)
  | .abandon record await => do
      let request : AbandonRequest := ⟨command.subject, record⟩
      let abandoned ← kernel (ObjectiveActivity.abandon config snapshot height request)
      if abandoned.await.id ≠ await then throw .staleAwait
      pure (.abandon request abandoned)
  | .invoke object _ method args grants envelope postage account _ => do
      let some value := decodeDataBytes args | throw .inputUndecodable
      let request := invokeRequest command object method value grants envelope postage account
      match ObjectiveCall.invoke config snapshot height request with
      | .ok invoked => pure (.invoke request invoked)
      | .error reason => throw (.call reason)
  | .deliverMessage sender target message => do
      let request := messageRequest command sender target message
      match ObjectiveSend.deliverMessage config snapshot height request with
      | .ok delivered => pure (.deliverMessage request delivered)
      | .error reason => throw (.message reason)
  | .adopt object _ pin stateType migration dropped law upgrade chosen envelope patience account _ => do
      let request := adoptRequest command object pin stateType migration dropped law upgrade chosen envelope patience
        account
      pure (.adopt request (← kernel (ObjectiveActivity.adopt config snapshot height request)))
  | .migrate object account _ => do
      let request := migrateRequest command object account
      pure (.migrate request (← kernel (ObjectiveActivity.migrate config snapshot height request)))
  | .abortDrained record await extra account _ => do
      let request : ObjectiveActivity.AbortRequest := ⟨command.subject, record, extra, account⟩
      let aborted ← kernel (ObjectiveActivity.abortDrained config snapshot height request)
      if aborted.await.id ≠ await then throw .staleAwait
      pure (.abortDrained request aborted)
  | .rebirth record await envelope => do
      let request : ObjectiveActivity.RebirthRequest := ⟨command.subject, record, envelope⟩
      let reborn ← kernel (ObjectiveActivity.rebirth config snapshot height request)
      if reborn.await.id ≠ await then throw .staleAwait
      pure (.rebirth request reborn)

def postStream : StreamCodec Post :=
  StreamCodec.xmap (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream))
    (fun post => (post.cell, post.pre, post.bytes)) (fun (cell, pre, bytes) => ⟨cell, pre, bytes⟩)
    (by intro post; cases post; rfl)

/-- The outcome a signer consents to: the decided turn's posts. -/
def outcomeDigest (posts : List Post) : Digest :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE.ACTIVITY.OUTCOME/v1".toUTF8.toList
    ((StreamCodec.list postStream).encode posts)).digest

/-! ## The signed request -/

/-- What the signature covers besides the command: the decided outcome, and
the marker. -/
structure Declaration where
  outcome : Digest
  operationNullifier : Nat

def declarationStream : StreamCodec Declaration :=
  StreamCodec.xmap (StreamCodec.product digestStream StreamCodec.nat)
    (fun d => (d.outcome, d.operationNullifier)) (fun (outcome, nullifier) => ⟨outcome, nullifier⟩)
    (by intro d; cases d; rfl)

def declarationCodec : LawfulCodec Declaration :=
  ResourceBirthCodec.strictCodec declarationStream.toLawful

def effectDigest (domain semantics : Digest) (command : Command) (d : Declaration) : Digest :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE.ACTIVITY.EFFECT/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product bytesStream bytesStream))).encode
      (domain, semantics, commandCodec.encode command, declarationCodec.encode d))).digest

/-- The resource a command's signed request targets: the object for a birth or
a state write, the account for a top-up, and the turn's own activity cell
otherwise. -/
def signedTarget (domain : Digest) (command : Command) : ResourceKind × Nat :=
  match command.turn with
  | .publish artifact _ _ _ =>
      (.object, (ObjectiveActivity.packageCell domain
        ((ObjectiveBendSourceArtifact.decode artifact).map ObjectiveBendSourceArtifact.identity |>.getD ⟨0⟩)).value)
  | .create object _ _ _ _ _ _ _ _ => (.object, object)
  | .birth object _ _ _ _ _ _ _ _ _ => (.object, object)
  | .resolve slot _ => (.object, (AnswerSlot.cell domain slot).value)
  | .deliver record _ _ _ _ => (.object, record.value)
  | .topUp _ account _ _ => (.account, account)
  | .exhaust record _ _ _ _ => (.object, record.value)
  | .abandon record _ => (.object, record.value)
  | .invoke object _ _ _ _ _ _ _ _ => (.object, object)
  | .deliverMessage sender target _ => (.object, (Inbox.cell domain sender target).value)
  | .adopt object _ _ _ _ _ _ _ _ _ _ _ _ => (.object, object)
  | .migrate object _ _ => (.object, object)
  | .abortDrained record _ _ _ _ => (.object, record.value)
  | .rebirth record _ _ => (.object, record.value)

def verbFor : (kind : ResourceKind) → Verb kind
  | .object => .mutateObject
  | .account => .transfer
  | .program => .installProgram

def contextAt (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (kind : ResourceKind) (target : Nat) : RequestContext where
  authority :=
    { kind := kind
      domain := snapshot.domain
      semantics := semantics
      federation := ambient.federation
      subject := command.subject
      subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.subject
      target := ⟨target⟩
      verb := verbFor kind
      nonce := marker snapshot.domain semantics command
      height := ambient.height
      policyId := ⟨target⟩
      policyEpoch := snapshot.authState.policyEpoch ⟨target⟩
      policyRevision := snapshot.authState.policyRevision ⟨target⟩
      cost := (commandCodec.encode command).length }
  argsDigestBytes := fun bytes =>
    (Sp800185Cshake256.hash "DREGG.OBJECTIVE.ACTIVITY.ARGS/v1".toUTF8.toList
      (commandCodec.encode command ++ bytes)).digest

/-- The request at one resource, over the decided outcome. -/
def requestAt (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (kind : ResourceKind) (target : Nat) (preRoot : Digest) (outcome : Digest) : PackedEffectRequest :=
  (contextAt snapshot semantics ambient command kind target).request declarationCodec
    (effectDigest snapshot.domain semantics command) preRoot
    (marker snapshot.domain semantics command) ⟨outcome, marker snapshot.domain semantics command⟩

/-- The signed request of a command. -/
def signedRequest (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (preRoot : Digest) (outcome : Digest) : PackedEffectRequest :=
  let (kind, target) := signedTarget snapshot.domain command
  requestAt snapshot semantics ambient command kind target preRoot outcome

/-! ## Who may: object holders and account owners -/

/-- The signer holds a capability admissible for mutating `object`. -/
def objectHolder (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (object : Nat) (capability : CapabilityId) (preRoot outcome : Digest) : Bool :=
  match readCapability snapshot.cell .object capability with
  | none => false
  | some stored =>
      match requestAt snapshot semantics ambient command .object object preRoot outcome with
      | ⟨.object, request⟩ => AuthorizationDeclaration.capabilityAdmissibleCheck stored.head snapshot.authState request
      | _ => false

/-- The signer owns `account` and may spend it. -/
def accountHolder (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (account : Nat) (capability : CapabilityId) (preRoot outcome : Digest) : Bool :=
  let stored := readCapability snapshot.cell .account capability
  decide (PayAssignmentReceiver.OwnerGrant stored command.subject account) &&
    match stored with
    | none => false
    | some stored =>
        match requestAt snapshot semantics ambient command .account account preRoot outcome with
        | ⟨.account, request⟩ => AuthorizationDeclaration.capabilityAdmissibleCheck stored.head snapshot.authState request
        | _ => false

/-- The authority a command needs beyond its signature. -/
def authorized (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command)
    (preRoot outcome : Digest) : Except Reject Unit :=
  let object (o : Nat) (c : CapabilityId) : Except Reject Unit :=
    if objectHolder snapshot semantics ambient command o c preRoot outcome then .ok () else .error .notObjectHolder
  let account (a : Nat) (c : CapabilityId) : Except Reject Unit :=
    if accountHolder snapshot semantics ambient command a c preRoot outcome then .ok () else .error .notAccountOwner
  match command.turn with
  | .resolve _ _ | .abandon _ _ | .deliverMessage _ _ _ | .rebirth _ _ _ => .ok ()
  | .adopt o oc _ _ _ _ _ _ _ _ _ a ac => do object o oc; account a ac
  | .migrate _ a ac => account a ac
  | .abortDrained _ _ extra a ac => if extra = zeroCapacity then .ok () else account a ac
  | .publish _ _ p pc => account p pc
  | .create o oc _ _ _ _ _ p pc => do object o oc; account p pc
  | .birth o oc a ac _ _ _ _ _ _ => do object o oc; account a ac
  | .deliver _ _ extra a ac | .exhaust _ _ extra a ac =>
      if extra = zeroCapacity then .ok () else account a ac
  | .topUp _ a ac _ => account a ac
  | .invoke o oc _ _ _ _ _ a ac => do object o oc; account a ac

/-! ## Preparation -/

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

structure Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) where
  private mk ::
  directory : LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot
  config : Config
  configExact : configOf deployment profile ambient = .ok config
  decided : Decided config durable.snapshot ambient.height command
  decidedExact : decideTurn config durable.snapshot ambient.height command = .ok decided
  preRoot : Digest
  preRootExact : preRoot = durable.snapshot.model.roots ⟨(signedTarget deployment.domain command).2⟩
  final : List Post × List ReadGuard
  finalExact : ActivitySeatEnd.finalize config durable.snapshot ambient.height decided = .ok final
  outcome : Digest
  outcomeExact : outcome = outcomeDigest final.1
  authorizedExact : authorized authority.snapshot profile.semantics ambient command preRoot outcome = .ok ()

def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) : Except Reject (Prepared deployment profile ambient durable command) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let snapshot := authority.snapshot
  if command.expectedAuthorityRoot ≠ snapshot.cell.root then throw .staleAuthority
  if snapshot.spent (marker snapshot.domain profile.semantics command) then throw .replayedMarker
  match configExact : configOf deployment profile ambient with
  | .error reason => throw (.kernel reason)
  | .ok config =>
    match decidedExact : decideTurn config durable.snapshot ambient.height command with
    | .error reason => throw reason
    | .ok decided =>
      match finalExact : ActivitySeatEnd.finalize config durable.snapshot ambient.height decided with
      | .error reason => throw (.seats reason)
      | .ok final =>
      let preRoot := durable.snapshot.model.roots ⟨(signedTarget deployment.domain command).2⟩
      let outcome := outcomeDigest final.1
      match authorizedExact : authorized snapshot profile.semantics ambient command preRoot outcome with
      | .error reason => throw reason
      | .ok () =>
        pure ⟨directory, authority, config, configExact, decided, decidedExact, preRoot, rfl, final, finalExact,
          outcome, rfl, authorizedExact⟩

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

def Prepared.request (prepared : Prepared deployment profile ambient durable command) : PackedEffectRequest :=
  signedRequest prepared.authority.snapshot profile.semantics ambient command prepared.preRoot prepared.outcome

/-! ## The receiver -/

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  (transactionOf ingress.command).getD ⟨marker domain semantics ingress.command⟩

def event (domain _semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.OBJECTIVE.ACTIVITY.EVENT/v1".toUTF8.toList ingress.bytes).digest
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (command : Command) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (marker domain semantics command)

/-- The exact charge of a turn's footprint. -/
def charge (ingress : DecodedIngress) (posts : List Post) (guards : List ReadGuard) : ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => posts.length + guards.length
  | .storageBytes => (posts.map fun post => post.bytes.length).sum
  | .witnessBytes => ingress.ingress.envelope.length
  | .proofWork => 2
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

/-- This receiver's sealing on the kernel turn: the authority guard, the signed
marker, the replay event carrying the signed ingress, the signer. -/
def admissionSeal (prepared : Prepared deployment profile ambient durable command) (ingress : DecodedIngress) : Seal :=
  ⟨prepared.authority.readGuards, [nullifier deployment.domain profile.semantics command],
    event deployment.domain profile.semantics ingress, some command.subject, charge ingress⟩

def Prepared.intent (prepared : Prepared deployment profile ambient durable command) (ingress : DecodedIngress) :
    DataIntent rootBytes :=
  ActivitySeatEnd.AdmittedTurn.finalIntent (admissionSeal prepared ingress) prepared.final.1 prepared.final.2
    prepared.decided

/-- A cell an activity intent writes is an activity cell or a seat cell (the seats
an ending activity held), each at its own protected coordinate; the Book; or a
cell the kernel retires: the registry's retired image at a protected coordinate
(an ended record or a settled slot). -/
def ActivityOrBook (deployment : Deployment) (write : DataWrite) : Prop :=
  write.cellId = ⟨deployment.resourceBookId⟩ ∨
    (∃ payload, ObjectiveActivity.payloadOf write.canonicalPostBytes = some payload ∧
      write.cellId.value = ObjectiveActivityCell.coordinate deployment.domain payload.role payload.key) ∨
    (∃ payload, SeatStore.payloadOf write.canonicalPostBytes = some payload ∧
      write.cellId.value = SeatCell.coordinate deployment.domain payload.role payload.key) ∨
    (write.canonicalPostBytes = ObjectiveActivity.retiredImage ∧ ObjectiveActivityCell.reservedBase ≤ write.cellId.value)

def activityCellAt (deployment : Deployment) (write : DataWrite) : Bool :=
  match ObjectiveActivity.payloadOf write.canonicalPostBytes with
  | some payload => decide (write.cellId.value = ObjectiveActivityCell.coordinate deployment.domain payload.role payload.key)
  | none => false

def seatCellAt (deployment : Deployment) (write : DataWrite) : Bool :=
  match SeatStore.payloadOf write.canonicalPostBytes with
  | some payload => decide (write.cellId.value = SeatCell.coordinate deployment.domain payload.role payload.key)
  | none => false

def retiredAt (write : DataWrite) : Bool :=
  decide (write.canonicalPostBytes = ObjectiveActivity.retiredImage ∧
    ObjectiveActivityCell.reservedBase ≤ write.cellId.value)

theorem activityOrBook_iff (deployment : Deployment) (write : DataWrite) :
    ActivityOrBook deployment write ↔
      (write.cellId = ⟨deployment.resourceBookId⟩ ∨ activityCellAt deployment write = true ∨
        seatCellAt deployment write = true ∨ retiredAt write = true) := by
  unfold ActivityOrBook activityCellAt seatCellAt retiredAt
  constructor
  · rintro (h | ⟨payload, hp, hat⟩ | ⟨payload, hp, hat⟩ | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl (by rw [hp]; simpa using hat))
    · exact Or.inr (Or.inr (Or.inl (by rw [hp]; simpa using hat)))
    · exact Or.inr (Or.inr (Or.inr (by simpa using h)))
  · rintro (h | h | h | h)
    · exact Or.inl h
    · split at h
      · rename_i payload hp; exact Or.inr (Or.inl ⟨payload, hp, by simpa using h⟩)
      · cases h
    · split at h
      · rename_i payload hp; exact Or.inr (Or.inr (Or.inl ⟨payload, hp, by simpa using h⟩))
      · cases h
    · exact Or.inr (Or.inr (Or.inr (by simpa using h)))

instance (deployment : Deployment) (write : DataWrite) : Decidable (ActivityOrBook deployment write) :=
  decidable_of_iff _ (activityOrBook_iff deployment write).symm

def PhysicalShape (prepared : Prepared deployment profile ambient durable command) (ingress : DecodedIngress) :
    Prop :=
  let intent := prepared.intent ingress
  (intent.writes.map DataWrite.cellId).Nodup ∧
    (∀ write ∈ intent.writes, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ intent.writes, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ write ∈ intent.writes, ActivityOrBook deployment write) ∧
    (∀ guard ∈ intent.readGuards, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

instance physicalShapeDecidable (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) : Decidable (PhysicalShape prepared ingress) := by
  unfold PhysicalShape
  infer_instance

structure Accepted [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile ambient durable ingress.command
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.envelope
  physical : PhysicalShape prepared ingress

def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (Accepted deployment profile ambient durable ingress)) := do
  match prepare deployment profile ambient durable ingress.command with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared ingress then
      let ⟨kind, request⟩ := prepared.request
      match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
          (marker prepared.authority.snapshot.domain profile.semantics ingress.command)
          request ingress.ingress.envelope with
      | .error reason => return .error (.signature reason)
      | .ok receipt =>
          if same : receipt.envelopeBytes = ingress.ingress.envelope then
            return .ok ⟨prepared, receipt, same, physical⟩
          else return .error (.signature (.envelope .invalidSignature))
    else return .error .physicalPreparation

variable [DecidableEq F] {ingress : DecodedIngress}

def intent (accepted : Accepted deployment profile ambient durable ingress) : DataIntent rootBytes :=
  accepted.prepared.intent ingress

/-- **Protected coordinates.** Every cell an accepted activity turn writes is
an activity cell at its own coordinate, the deployment's Book, or a retirement
(the registry's retired image) at a protected coordinate. -/
theorem intent_writes_activity_or_book (accepted : Accepted deployment profile ambient durable ingress) :
    ∀ write ∈ (intent accepted).writes, ActivityOrBook deployment write :=
  accepted.physical.2.2.2.1

/-- Every write of an accepted turn satisfies the registry's loaded-and-final law. -/
theorem intent_writes_lawful (accepted : Accepted deployment profile ambient durable ingress) :
    ∀ write ∈ (intent accepted).writes, ResourceBirthController.Concrete.PhysicalPostLaw deployment write :=
  accepted.physical.2.2.1

/-- **Only an object holder births.** An accepted birth's signer holds a
capability admissible for mutating the object it names. -/
theorem birth_requires_object_holder (accepted : Accepted deployment profile ambient durable ingress)
    {object account deposit : Nat} {envelope resume timeout : Capacity}
    {objectCapability accountCapability : CapabilityId} {pin : Digest} {input : List UInt8}
    (turn : ingress.command.turn = .birth object objectCapability account accountCapability pin input envelope
      resume timeout deposit) :
    objectHolder accepted.prepared.authority.snapshot profile.semantics ambient ingress.command object
        objectCapability accepted.prepared.preRoot accepted.prepared.outcome = true ∧
      accountHolder accepted.prepared.authority.snapshot profile.semantics ambient ingress.command account
        accountCapability accepted.prepared.preRoot accepted.prepared.outcome = true := by
  have ok := accepted.prepared.authorizedExact
  unfold authorized at ok
  rw [turn] at ok
  by_cases held : objectHolder accepted.prepared.authority.snapshot profile.semantics ambient ingress.command
      object objectCapability accepted.prepared.preRoot accepted.prepared.outcome = true
  · by_cases owned : accountHolder accepted.prepared.authority.snapshot profile.semantics ambient
        ingress.command account accountCapability accepted.prepared.preRoot accepted.prepared.outcome = true
    · exact ⟨held, owned⟩
    · simp [held, owned, bind, Except.bind] at ok
  · simp [held, bind, Except.bind] at ok

/-- **Only an object holder makes an object.** An accepted creation's signer
holds a capability admissible for mutating the object resource, and owns the
payer account it names. -/
theorem create_requires_object_holder (accepted : Accepted deployment profile ambient durable ingress)
    {object payer : Nat} {objectCapability payerCapability : CapabilityId} {pin : Digest}
    {stateType : Minidregg.Theory.ObjectiveBendTypes.Ty} {law : Minidregg.Pred.Pred}
    {upgrade : ObjectRecord.UpgradePolicy} {seed : Option (List UInt8)}
    (turn : ingress.command.turn = .create object objectCapability pin stateType law upgrade seed payer
      payerCapability) :
    objectHolder accepted.prepared.authority.snapshot profile.semantics ambient ingress.command object
        objectCapability accepted.prepared.preRoot accepted.prepared.outcome = true ∧
      accountHolder accepted.prepared.authority.snapshot profile.semantics ambient ingress.command payer
        payerCapability accepted.prepared.preRoot accepted.prepared.outcome = true := by
  have ok := accepted.prepared.authorizedExact
  unfold authorized at ok
  rw [turn] at ok
  by_cases held : objectHolder accepted.prepared.authority.snapshot profile.semantics ambient ingress.command
      object objectCapability accepted.prepared.preRoot accepted.prepared.outcome = true
  · by_cases owned : accountHolder accepted.prepared.authority.snapshot profile.semantics ambient
        ingress.command payer payerCapability accepted.prepared.preRoot accepted.prepared.outcome = true
    · exact ⟨held, owned⟩
    · simp [held, owned, bind, Except.bind] at ok
  · simp [held, bind, Except.bind] at ok

/-- **A native birth runs the object's pinned package.** The birth an accepted
command commits is on a cell that has an object record (at the Host's own
snapshot), and that record pins exactly the package the command names: an
object without a record is refused `notAnObject`, another pin `pinMismatch`. -/
theorem native_birth_on_pinned_object (accepted : Accepted deployment profile ambient durable ingress)
    {request : BirthRequest} {born : Birth accepted.prepared.config durable.snapshot ambient.height request}
    {signed : request.predecessor = none} (_decided : accepted.prepared.decided = .birth request signed born) :
    ∃ object : ObjectRecord.ObjectRecord,
      ObjectiveActivity.readObject accepted.prepared.config durable.snapshot request.object = .ok (some object) ∧
        object.activePin = request.pin :=
  ⟨born.object, born.objectExact, born.pinned⟩

/-- A refusing ownership check refuses the whole command, whatever the kernel
decided (`notObjectHolder` is named). -/
theorem stranger_birth_refused {snapshot : Snapshot} {semantics : Digest} {object account deposit : Nat}
    {envelope resume timeout : Capacity} {objectCapability accountCapability : CapabilityId} {pin : Digest}
    {input : List UInt8} {preRoot outcome : Digest}
    (turn : command.turn = .birth object objectCapability account accountCapability pin input envelope
      resume timeout deposit)
    (stranger : objectHolder snapshot semantics ambient command object objectCapability preRoot outcome = false) :
    authorized snapshot semantics ambient command preRoot outcome = .error .notObjectHolder := by
  unfold authorized
  rw [turn]
  simp [stranger, bind, Except.bind]

/-- **The native delivery is the kernel delivery.** An accepted deliver
command commits exactly the kernel's `Delivery.intent` under this receiver's
seal; so consume-once (`ObjectiveActivity.resume_consumes_once`, stated for
every sealing) holds of what the Host commits. -/
theorem native_delivery_consumes_once
    (accepted : Accepted deployment profile ambient durable ingress)
    {request : DeliverRequest}
    {delivery : Delivery accepted.prepared.config durable.snapshot ambient.height request}
    (decided : accepted.prepared.decided = .deliver request delivery)
    {next : DataSnapshot rootBytes}
    (installed : DurableDataIntent.execute .complete durable.snapshot (intent accepted) = .accepted next) :
    (∀ (later : DataIntent rootBytes), ObjectiveActivity.awaitClaim delivery.await.id ∈ later.nullifiers →
      ∀ schedule after, DurableDataIntent.execute schedule next later ≠ .accepted after) ∧
    (∀ schedule, DurableDataIntent.execute schedule next (intent accepted) = .replayed (intent accepted).erase) := by
  have carries : ObjectiveActivity.awaitClaim delivery.await.id ∈ (intent accepted).nullifiers := by
    simp [intent, Prepared.intent, decided, ActivitySeatEnd.AdmittedTurn.finalIntent, delivery.claimsExact]
  exact ⟨fun later again schedule after =>
      ObjectiveActivity.spent_claim_never_accepted carries installed later again schedule after,
    ObjectiveActivity.installed_retry_replays installed⟩

/-- **An ending activity closes the seats it holds, natively.** When an accepted
turn ends an activity (a birth or delivery that finishes or faults, or an
abandonment) whose holdings cell lists seats, the turn commits the joint posts
(`ActivitySeatEnd.Joined.rewrite`: the activity's own, its Book post replaced
by the joint batch's, and the retired cells of the closed seats), every held seat that was open
is gone from the world (and `Joined.deregisters`, `Joined.retires` say its account and cell are closed), and the Book is the activity's batch followed by the seat closing,
admitted together on the loaded Book. -/
theorem native_end_closes_held_seats (accepted : Accepted deployment profile ambient durable ingress)
    {record : Nat} {pre : ObjectiveActivity.BookCell} {posted : ObjectiveActivity.Postings pre}
    (ends : ActivitySeatEnd.AdmittedTurn.ending accepted.prepared.decided = some (record, ⟨pre, posted⟩))
    (holds : SeatStore.readHoldings durable.snapshot accepted.prepared.config.domain record ≠ []) :
    ∃ joined : ActivitySeatEnd.Joined accepted.prepared.config durable.snapshot ambient.height record posted,
      accepted.prepared.final.1 = joined.rewrite accepted.prepared.decided.posts ∧
      (∀ seat ∈ Seats.heldOpen (joined.held.loaded.world
          (posted.batch.apply (Theory.CanonicalResourceKernel.logicalBook pre.logical))) ambient.height record,
        ∀ after ∈ joined.held.next.seats, after.account ≠ seat.account) ∧
      Seats.Posts (Theory.CanonicalResourceKernel.logicalBook pre.logical)
        (Seats.seqBatch posted.batch joined.held.batch) joined.held.next.book := by
  have final := accepted.prepared.finalExact
  unfold ActivitySeatEnd.finalize at final
  rw [ends] at final
  simp only at final
  split at final
  · cases final
  · rename_i none_
    exact absurd (ActivitySeatEnd.join_none none_) holds
  · rename_i joined _
    have same := (Except.ok.inj final).symm
    exact ⟨joined, by rw [same], joined.closes.1, joined.closes.2.1⟩

/-- **The native delivery's fields bind the stored checkpoint** (the kernel's
projection `delivery_fields_bind_checkpoint`, at the Host's own snapshot). -/
theorem native_delivery_fields_bind_checkpoint
    (accepted : Accepted deployment profile ambient durable ingress)
    {request : DeliverRequest}
    {delivery : Delivery accepted.prepared.config durable.snapshot ambient.height request}
    (_decided : accepted.prepared.decided = .deliver request delivery) :
    ∃ record state,
      ObjectiveActivity.readRecord durable.snapshot request.record = some record ∧
      record.phase = .awaiting delivery.await ∧
      delivery.await.id = ObjectiveActivity.awaitId request.record record.generation
        (checkpointDigest record.checkpoint) ∧
      decodeCheckpoint record.checkpoint = some state ∧
      Minidregg.Theory.ObjectiveBendDemandMachine.resume
        (ObjectiveActivity.responseData delivery.settlement.decided delivery.view).term state =
          some delivery.resumed :=
  let ⟨record, state, a, b, c, d, e, _⟩ := ObjectiveActivity.delivery_fields_bind_checkpoint delivery
  ⟨record, state, a, b, c, d, e⟩

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (domain semantics : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨transactionId domain semantics ingress, (event domain semantics ingress).eventId⟩

/-- A retained ingress finds its record by its transaction id: the exact
ingress replays, any other ingress under the same id (another delivery of the
same await, another decision of the same slot) is a conflict. -/
def replay (domain semantics : Digest) (durable : Durable) (ingress : DecodedIngress) :
    Option (Except Unit Receipt) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded
      (transactionId domain semantics ingress) durable.snapshot.model.journal with
  | none => none
  | some recorded =>
    if recorded.transactionId = transactionId domain semantics ingress ∧
        recorded.event.event = event domain semantics ingress then
      some (.ok (receipt domain semantics ingress))
    else some (.error ())

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | rejected (reason : Reject)
  | transactionConflict
  | durableRejected (reason : DurableDataIntent.RejectReason)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveLoaded (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    (bytes : List UInt8) : IO Result := do
  let some ingress := decodeIngress bytes
    | return .rejected .malformedIngress
  match replay deployment.domain profile.semantics durable ingress with
  | some (.ok prior) => return .confirmed .replayed prior
  | some (.error _) => return .transactionConflict
  | none =>
    match ← admitDecodedNative deployment profile ambient durable native ingress with
    | .error reason => return .rejected reason
    | .ok accepted =>
      match ← DurableReceiverIO.receiveLoaded transport rootBytes durable (intent accepted) with
      | .confirmed kind _ => return .confirmed kind (receipt deployment.domain profile.semantics ingress)
      | .rejected reason => return .durableRejected reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

/-! ## Signing plan -/

/-- The exact header the signer signs. When the kernel refuses the command, the
header is built over the empty outcome and the submission is refused with the
named reason. -/
def signingHeader (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let some authority := loadDeployment deployment durable.snapshot
    | .error "authority unavailable"
  let outcome := match configOf deployment profile ambient with
    | .ok config => match decideTurn config durable.snapshot ambient.height command with
      | .ok decided => match ActivitySeatEnd.finalize config durable.snapshot ambient.height decided with
        | .ok final => outcomeDigest final.1
        | .error _ => outcomeDigest []
      | .error _ => outcomeDigest []
    | .error _ => outcomeDigest []
  let preRoot := durable.snapshot.model.roots ⟨(signedTarget deployment.domain command).2⟩
  (CredentialSignatureAdmission.signingHeader authority.snapshot
    (marker deployment.domain profile.semantics command)
    (signedRequest authority.snapshot profile.semantics ambient command preRoot outcome)).mapError
      (fun reason => s!"activity signer key: {repr reason}")

/-- What the decided turn returns to its signer, shown before it signs: an
invocation's root result, a delivered message's reply (their data bytes);
nothing for every other turn. It is
a function of the snapshot and the command, so every replay recomputes it. -/
def Decided.report {rootBytes : List UInt8 → Digest} {config : Config} {snapshot : DataSnapshot rootBytes}
    {height : Nat} {command : Command} : Decided config snapshot height command → List UInt8
  | .invoke _ invoked => dataBytes invoked.result
  | .deliverMessage _ delivered => match delivered.outcome with
    | .replied result _ => dataBytes result
    | .failed _ => []
  | _ => []

/-- The report of a command at a durable snapshot (empty when it is refused). -/
def planReport (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) : List UInt8 :=
  match configOf deployment profile ambient with
  | .ok config => match decideTurn config durable.snapshot ambient.height command with
    | .ok decided => decided.report
    | .error _ => []
  | .error _ => []

structure SigningPlan where
  domain : Digest
  semantics : Digest
  commandBytes : List UInt8
  header : List UInt8
  /-- `Decided.report`: what the turn returns (an invocation's result). Not signed:
  the header binds the turn's posts, and the report is recomputed from them. -/
  report : List UInt8
  deriving DecidableEq, Repr

def signingPlanStream : StreamCodec SigningPlan :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product bytesStream (StreamCodec.product bytesStream bytesStream))))
    (fun plan => (plan.domain, plan.semantics, plan.commandBytes, plan.header, plan.report))
    (fun (domain, semantics, command, header, report) => ⟨domain, semantics, command, header, report⟩)
    (by intro plan; cases plan; rfl)

/-- v2 carries the report; a v1 plan refuses to decode. -/
def signingPlanCodec : LawfulCodec SigningPlan :=
  ObjectiveActivityWire.framed "DREGG/OBJECTIVE/ACTIVITY/PLAN/v2".toUTF8.toList signingPlanStream

#assert_axioms command_roundtrip
#assert_axioms command_canonical
#assert_axioms intent_writes_activity_or_book
#assert_axioms intent_writes_lawful
#assert_axioms birth_requires_object_holder
#assert_axioms create_requires_object_holder
#assert_axioms native_birth_on_pinned_object
#assert_axioms stranger_birth_refused
#assert_axioms native_delivery_consumes_once
#assert_axioms native_delivery_fields_bind_checkpoint
#assert_axioms native_end_closes_held_seats

end Minidregg.Kernel.ObjectiveActivityReceiver
