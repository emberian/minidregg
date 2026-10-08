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

**Receipt retrieval and retries.** Possession of the original signed request is
enough to retrieve its recorded receipt: replaying those exact bytes takes the
`exact` route with no fresh signature check, including after the subject rotates
its key. A retry whose invocation is re-signed under the same operation id takes
the `retry` route and must pass `verifyRetry` under the subject's **current** key.
Neither route commits anything, whether retry verification succeeds or fails.

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
import Kernel.PayAssignmentOwner

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
  send, with the send's continuation allowance; the sends' allowances total at most
  `allowance` (GPT-6 row F). Only a holder of a capability on `object`, spending an account
  it owns. -/
  | invoke (object : Nat) (objectCapability : CapabilityId) (method : String) (args : List UInt8)
      (grants : List ObjectiveCall.Grant) (envelope postage : Capacity) (allowance : Nat) (account : Nat)
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
  /-- Register an invariant domain (`ObjectiveDomain.register`): the `members` (each with a
  capability the signer holds on it; each member's upgrade policy must consent), their joint
  `law` (which must hold now), funded by `payer`, which pays the public price of `envelope` (whose
  `domainWork` must cover the turn end's judgment of the new domain). -/
  | registerDomain (members : List (Nat × CapabilityId)) (law : Minidregg.Pred.Pred) (payer : Nat)
      (payerCapability : CapabilityId) (envelope : Capacity)
  deriving DecidableEq, Repr

abbrev CreateWire :=
  Nat × CapabilityId × Digest × Minidregg.Theory.ObjectiveBendTypes.Ty × Minidregg.Pred.Pred ×
    ObjectRecord.UpgradePolicy × Option (List UInt8) × Nat × CapabilityId
abbrev PublishWire := List UInt8 × List UInt8 × Nat × CapabilityId
abbrev BirthWire :=
  Nat × CapabilityId × Nat × CapabilityId × Digest × List UInt8 × Capacity × Capacity × Capacity × Nat
abbrev EndWire := Digest × Digest × Capacity × Nat × CapabilityId
abbrev InvokeWire :=
  Nat × CapabilityId × String × List UInt8 × List ObjectiveCall.Grant × Capacity × Capacity × Nat × Nat ×
    CapabilityId
abbrev AdoptWire :=
  Nat × CapabilityId × Digest × Minidregg.Theory.ObjectiveBendTypes.Ty × Option String × List String ×
    Minidregg.Pred.Pred × ObjectRecord.UpgradePolicy × List Digest × Capacity × Nat × Nat × CapabilityId

abbrev RegisterWire := List (Nat × CapabilityId) × Minidregg.Pred.Pred × Nat × CapabilityId × Capacity

abbrev TurnWire :=
  Sum PublishWire (Sum CreateWire (Sum BirthWire (Sum (Digest × AnswerWire) (Sum EndWire
    (Sum (Digest × Nat × CapabilityId × Nat)
      (Sum EndWire (Sum (Digest × Digest) (Sum InvokeWire (Sum (Nat × Nat × Digest)
        (Sum AdoptWire (Sum (Nat × Nat × CapabilityId) (Sum EndWire (Sum (Digest × Digest × Capacity) RegisterWire)))))))))))))

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
  | .invoke o oc method args grants envelope postage allowance a ac =>
      .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
        (o, oc, method, args, grants, envelope, postage, allowance, a, ac)))))))))
  | .deliverMessage sender target message =>
      .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (sender, target, message))))))))))
  | .adopt o oc pin st mig dropped law upgrade chosen envelope patience a ac =>
      .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (o, oc, pin, st, mig, dropped, law, upgrade, chosen, envelope, patience, a, ac)))))))))))
  | .migrate o a ac => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (o, a, ac))))))))))))
  | .abortDrained record await extra a ac => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (record, await, extra, a, ac)))))))))))))
  | .rebirth record await envelope => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (record, await, envelope))))))))))))))
  | .registerDomain members law p pc envelope => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ((members, law, p, pc, envelope)))))))))))))))

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
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      (o, oc, method, args, grants, envelope, postage, allowance, a, ac))))))))) =>
      .invoke o oc method args grants envelope postage allowance a ac
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (sender, target, message)))))))))) =>
      .deliverMessage sender target message
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (o, oc, pin, st, mig, dropped, law, upgrade, chosen, envelope, patience, a, ac))))))))))) =>
      .adopt o oc pin st mig dropped law upgrade chosen envelope patience a ac
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (o, a, ac)))))))))))) => .migrate o a ac
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (record, await, extra, a, ac))))))))))))) => .abortDrained record await extra a ac
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (record, await, envelope)))))))))))))) => .rebirth record await envelope
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ((members, law, p, pc, envelope))))))))))))))) => .registerDomain members law p pc envelope

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
        (StreamCodec.product capacityStream (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat capabilityIdStream))))))))

def adoptStream : StreamCodec AdoptWire :=
  StreamCodec.product StreamCodec.nat (StreamCodec.product capabilityIdStream
    (StreamCodec.product digestStream (StreamCodec.product ObjectStateType.tyStream
      (StreamCodec.product (StreamCodec.option stringStream) (StreamCodec.product (StreamCodec.list stringStream)
        (StreamCodec.product LawLeaf.predStream (StreamCodec.product ObjectRecord.upgradeStream
          (StreamCodec.product (StreamCodec.list digestStream) (StreamCodec.product capacityStream
            (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat capabilityIdStream)))))))))))

def registerStream : StreamCodec RegisterWire :=
  StreamCodec.product (StreamCodec.list (StreamCodec.product StreamCodec.nat capabilityIdStream))
    (StreamCodec.product LawLeaf.predStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product capabilityIdStream capacityStream)))

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
                      (StreamCodec.sum (StreamCodec.product digestStream (StreamCodec.product digestStream capacityStream))
                        registerStream))))))))))))))
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

/-- v10: `invoke` carries the signer's continuation `allowance` (GPT-6 row F); v9: the turn sum ends
with `registerDomain` (`ObjectiveDomain`); v8: an `invoke`'s grants are v2 (`ObjectiveCall.grantStream`: code, arguments bound, caller);
v7: envelopes carry the extraction tick lane (`Capacity.extractTicks`); v6: the upgrade turns
(`adopt`, `migrate`, `abortDrained`, `rebirth`) join the sum, and `create` declares the object's
state type (`ObjectStateType.tyStream`); v5: `create` carries an optional initial declared state,
and the turn sum has no `writeState`; v9 (and older) commands refuse to decode. -/
-- v11: envelopes carry `replayBytes`, `coreBytes` (GPT-6 row E work account); a v10 command does not decode.
-- v12: envelopes carry `domainWork`, and `registerDomain` carries its envelope and the paying
-- account and capability (A3 domain pricing); a v11 command does not decode.
def commandFrame : List UInt8 := "DREGG/OBJECTIVE/ACTIVITY/COMMAND/v12".toUTF8.toList

def commandCodec : LawfulCodec Command := ObjectiveActivityWire.framed commandFrame commandStream

/-- A v9 command (before the invoke carried its continuation allowance) refuses to decode. -/
theorem command_v9_refuses (body : List UInt8) :
    commandCodec.decode ("DREGG/OBJECTIVE/ACTIVITY/COMMAND/v9".toUTF8.toList ++ body) = none := by
  cases found : commandCodec.decode ("DREGG/OBJECTIVE/ACTIVITY/COMMAND/v9".toUTF8.toList ++ body) with
  | none => rfl
  | some command =>
    have canon := ObjectiveActivityWire.framed_canonical found
    have cut := congrArg (List.take "DREGG/OBJECTIVE/ACTIVITY/COMMAND/v9".toUTF8.toList.length) canon
    change (commandFrame ++ commandStream.encode command).take _ =
      ("DREGG/OBJECTIVE/ACTIVITY/COMMAND/v9".toUTF8.toList ++ body).take _ at cut
    rw [List.take_append_of_le_length (by decide +kernel), List.take_left' rfl] at cut
    exact absurd cut (by decide +kernel)

theorem command_roundtrip (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

theorem command_canonical {bytes : List UInt8} {command : Command}
    (accepted : commandCodec.decode bytes = some command) : commandCodec.encode command = bytes :=
  ObjectiveActivityWire.framed_canonical accepted

/-- The signed ingress: the command, the OUTCOME the signer signed (the digest of the decided
turn's posts at its plan, `outcomeDigest`), and the signed envelope. The outcome travels with
the ingress so that the signature is checked BEFORE the turn is decided (GPT-6 row E): the
receiver rebuilds the signed request from the command and this claim, verifies it, and only
then decides; a decided outcome other than the claim commits a charged failure
(`Reject.outcomeMoved`), never the claim's effects. -/
structure Ingress where
  commandBytes : List UInt8
  outcome : Digest
  envelope : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream (StreamCodec.product digestStream bytesStream))
    (fun ingress => (ingress.commandBytes, ingress.outcome, ingress.envelope))
    (fun (command, outcome, envelope) => ⟨command, outcome, envelope⟩)
    (by intro ingress; cases ingress; rfl)

/-- v2: the ingress carries the signed outcome (GPT-6 row E: signature before decision); a v1
ingress does not decode. -/
def ingressFrame : List UInt8 := "DREGG/OBJECTIVE/ACTIVITY/SIGNED/v2".toUTF8.toList

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
    (grants : List ObjectiveCall.Grant) (envelope postage : Capacity) (allowance account : Nat) :
    ObjectiveCall.InvokeRequest :=
  ⟨command.subject, ⟨object⟩, method, args, grants, envelope, account, command.nonce, postage, allowance⟩

def messageRequest (command : Command) (sender target : Nat) (message : Digest) : ObjectiveSend.MessageRequest :=
  ⟨command.subject, sender, target, message⟩

def adoptRequest (command : Command) (object : Nat) (pin : Digest) (stateType : Minidregg.Theory.ObjectiveBendTypes.Ty)
    (migration : Option String) (dropped : List String) (law : Minidregg.Pred.Pred)
    (upgrade : ObjectRecord.UpgradePolicy) (rebirth : List Digest) (envelope : Capacity) (patience account : Nat) :
    ObjectiveActivity.AdoptRequest :=
  ⟨command.subject, ⟨object⟩, pin, stateType, migration, dropped, law, upgrade, rebirth, envelope, patience, account,
    command.nonce⟩

def registerRequest (command : Command) (members : List (Nat × CapabilityId)) (law : Minidregg.Pred.Pred)
    (payer : Nat) (envelope : Capacity) : ObjectiveActivity.RegisterRequest :=
  ⟨command.subject, members.map fun (member, _) => ⟨member⟩, law, payer, envelope, command.nonce⟩

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
  | .invoke object _ method args grants envelope postage allowance account _ =>
      (decodeDataBytes args).map fun value =>
        ObjectiveCall.invokeTransaction
          (invokeRequest command object method value grants envelope postage allowance account)
  | .deliverMessage _ _ message => some (ObjectiveSend.messageTransaction message)
  | .adopt object _ pin stateType migration dropped law upgrade chosen envelope patience account _ =>
      some (ObjectiveActivity.adoptTransaction
        (adoptRequest command object pin stateType migration dropped law upgrade chosen envelope patience account))
  | .migrate object account _ => some (ObjectiveActivity.migrateTransaction (migrateRequest command object account))
  | .abortDrained _ await _ _ _ => some (ObjectiveActivity.abortTransaction await)
  | .rebirth _ await _ => some (ObjectiveActivity.rebirthTransaction await)
  | .registerDomain members law payer _ envelope =>
      some (ObjectiveActivity.registerTransaction (registerRequest command members law payer envelope))

/-- Refusals of this receiver: the kernel's, the authority's, the ingress's. -/
inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | staleAuthority
  | replayedMarker | physicalPreparation | inputUndecodable
  | kernel (reason : ObjectiveActivity.Refusal)
  /-- The ending activity's held seats could not be closed (`ActivitySeatEnd.join`). -/
  | seats (reason : SeatStore.Refusal)
  /-- The call tree of an `invoke` was refused (re-entry, a law, a grant, a fault), with the front
  end the turn had drawn at the failure point (cv 01a117cd-857b): the budget that reaches it. -/
  | call (reason : ObjectiveCall.CallRefusal) (drawn : ObjectiveCall.FrontEnd)
  /-- A message delivery was refused (no inbox, an empty or moved head, its reply slot). -/
  | message (reason : ObjectiveSend.MessageRefusal)
  /-- The command's await is not the one the record awaits now. -/
  | staleAwait
  /-- The signer holds no capability admissible for mutating the object. -/
  | notObjectHolder
  /-- The signer does not own the Book account the turn spends or names as payer. -/
  | notAccountOwner
  /-- The turn decided an outcome other than the one its signer signed (`claimed`): its plan went
  stale. Like a reverted transaction's gas, a paying turn is CHARGED for the attempt (a
  charged failure, `Failed`); the signer re-plans on that receipt. -/
  | outcomeMoved (claimed decided : Digest)
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
  | .invoke object _ method args grants envelope postage allowance account _ => do
      let some value := decodeDataBytes args | throw .inputUndecodable
      let request := invokeRequest command object method value grants envelope postage allowance account
      match ObjectiveCall.invoke config snapshot height request with
      | .ok invoked => pure (.invoke request invoked)
      | .error (reason, drawn) => throw (.call reason drawn)
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
  | .registerDomain members law payer _ envelope => do
      let request := registerRequest command members law payer envelope
      pure (.registerDomain request (← kernel (ObjectiveActivity.register config snapshot height request)))

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
  | .invoke object _ _ _ _ _ _ _ _ _ => (.object, object)
  | .deliverMessage sender target _ => (.object, (Inbox.generationCell domain sender target).value)
  | .adopt object _ _ _ _ _ _ _ _ _ _ _ _ => (.object, object)
  | .migrate object _ _ => (.object, object)
  | .abortDrained record _ _ _ _ => (.object, record.value)
  | .rebirth record _ _ => (.object, record.value)
  | .registerDomain members law _ _ _ =>
      (.object, (ObjectiveActivity.domainCell domain
        (ObjectiveActivity.domainId (members.map fun (member, _) => ⟨member⟩) law)).value)

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
  | .invoke o oc _ _ _ _ _ _ a ac => do object o oc; account a ac
  | .registerDomain members _ p pc _ => do
      members.forM fun (o, oc) => object o oc
      account p pc

/-! ## Preparation -/

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

/-! ## The gate: authority, capability and funding, BEFORE anything is decided (GPT-6 row E)

Until row E the receiver decided the turn (the front end's replay, the type check, the run, the
extraction, the law) and only then checked the signature: the signed effect digest committed to
the decided outcome, so the outcome had to exist first, and a forged or unauthorized birth cost
the validator a whole turn for free. Now the ingress carries the outcome its signer signed
(`Ingress.outcome`), and the order is: decode; the authority image, the marker and the
configuration; the capabilities over the CLAIMED outcome (`authorized`); the payer's funds
(`funding`); the signature; and only then the decision. -/

/-- What a paying turn must be able to pay before it runs: the payer account and the public
price of its declared envelope plus what the turn moves out of the account (a birth's deposit). -/
def payment (config : Config) (command : Command) : Option (Nat × Nat) :=
  match command.turn with
  | .birth _ _ account _ _ _ envelope _ _ deposit => some (account, config.tariff.workOf envelope + deposit)
  | .invoke _ _ _ _ _ envelope _ _ account _ => some (account, config.tariff.workOf envelope)
  | _ => none

/-- **Funding before the run.** A paying turn whose account cannot pay is refused `unfunded`
before it is decided. -/
def funding (config : Config) (durable : Durable) (command : Command) : Except Reject Unit :=
  match payment config command with
  | none => .ok ()
  | some (account, price) =>
    match ObjectiveActivity.loadBook config durable.snapshot with
    | .error reason => .error (.kernel reason)
    | .ok book =>
      let available := (Theory.CanonicalResourceKernel.logicalBook book.logical).balance account config.asset
      if (price : Int) ≤ available then .ok () else .error (.kernel (.unfunded available price))

/-- A command that passed the gate, for the outcome its signer claims: the loaded authority,
the configuration, the capabilities over the claim, and the funds. Built only by `gate`; the
decision (`prepare`) takes one, so nothing is decided for a command that did not pass it. -/
structure Gated {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) (claimed : Digest) where
  private mk ::
  directory : LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot
  config : Config
  configExact : configOf deployment profile ambient = .ok config
  preRoot : Digest
  preRootExact : preRoot = durable.snapshot.model.roots ⟨(signedTarget deployment.domain command).2⟩
  authorizedExact : authorized authority.snapshot profile.semantics ambient command preRoot claimed = .ok ()
  funded : funding config durable command = .ok ()

def gate {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) (claimed : Digest) : Except Reject (Gated deployment profile ambient durable command claimed) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let snapshot := authority.snapshot
  if command.expectedAuthorityRoot ≠ snapshot.cell.root then throw .staleAuthority
  if snapshot.spent (marker snapshot.domain profile.semantics command) then throw .replayedMarker
  match configExact : configOf deployment profile ambient with
  | .error reason => throw (.kernel reason)
  | .ok config =>
    let preRoot := durable.snapshot.model.roots ⟨(signedTarget deployment.domain command).2⟩
    match authorizedExact : authorized snapshot profile.semantics ambient command preRoot claimed with
    | .error reason => throw reason
    | .ok () =>
      match funded : funding config durable command with
      | .error reason => throw reason
      | .ok () => pure ⟨directory, authority, config, configExact, preRoot, rfl, authorizedExact, funded⟩

/-- The signed request a gated command's signature must cover: over the CLAIMED outcome. -/
def Gated.request {F : Type} [Field F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
    {command : Command} {claimed : Digest} (gated : Gated deployment profile ambient durable command claimed) :
    PackedEffectRequest :=
  signedRequest gated.authority.snapshot profile.semantics ambient command gated.preRoot claimed

/-- **An unfunded request has no gate**, so nothing is decided for it (`prepare` takes a
`Gated`). -/
theorem unfunded_not_gated {F : Type} [Field F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
    {command : Command} {claimed : Digest} {config : Config} {reason : Reject}
    (configured : configOf deployment profile ambient = .ok config)
    (unfunded : funding config durable command = .error reason) :
    ¬ Nonempty (Gated deployment profile ambient durable command claimed) := fun ⟨gated⟩ => by
  have same : gated.config = config := Except.ok.inj (gated.configExact.symm.trans configured)
  have funded := gated.funded
  rw [same, unfunded] at funded
  cases funded

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
  finalExact : ActivitySeatEnd.finish config durable.snapshot ambient.height decided = .ok final
  outcome : Digest
  outcomeExact : outcome = outcomeDigest final.1
  authorizedExact : authorized authority.snapshot profile.semantics ambient command preRoot outcome = .ok ()

/-- The decision of a gated command (after its signature verified): the kernel turn, the seat
and domain end, and the outcome, which must be the one the signer claimed. -/
def prepare {F : Type} [Field F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
    {command : Command} {claimed : Digest} (gated : Gated deployment profile ambient durable command claimed) :
    Except Reject (Prepared deployment profile ambient durable command) :=
  match decidedExact : decideTurn gated.config durable.snapshot ambient.height command with
  | .error reason => .error reason
  | .ok decided =>
    match finalExact : ActivitySeatEnd.finish gated.config durable.snapshot ambient.height decided with
    | .error (.seats reason) => .error (.seats reason)
    | .error (.kernel reason) => .error (.kernel reason)
    | .ok final =>
      if same : claimed = outcomeDigest final.1 then
        .ok ⟨gated.directory, gated.authority, gated.config, gated.configExact, decided, decidedExact,
          gated.preRoot, gated.preRootExact, final, finalExact, claimed, same, gated.authorizedExact⟩
      else .error (.outcomeMoved claimed (outcomeDigest final.1))

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

def Prepared.request (prepared : Prepared deployment profile ambient durable command) : PackedEffectRequest :=
  signedRequest prepared.authority.snapshot profile.semantics ambient command prepared.preRoot prepared.outcome

/-- **A claimed operation never admits again**: once the signer's marker (for
an invocation, `(subject, opId)`) is spent, the GATE refuses `replayedMarker`
before verifying or deciding anything, whatever the command's content or the outcome it claims.
The same op id with a different call is refused here; the same call is answered first by `replay`. -/
theorem gate_spent_refused {directory : LoadedDirectory durable}
    {authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot} {claimed : Digest}
    (dir : loadDirectory durable = some directory)
    (auth : loadDeployment deployment durable.snapshot = some authority)
    (current : command.expectedAuthorityRoot = authority.snapshot.cell.root)
    (spent : authority.snapshot.spent (marker authority.snapshot.domain profile.semantics command) = true) :
    gate deployment profile ambient durable command claimed = .error .replayedMarker := by
  simp only [gate, requireSome, dir, auth]
  simp [bind, Except.bind, current, spent]
  rfl

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

/-- This receiver's sealing on a turn: the authority guard, the signed marker, the replay event
carrying the signed ingress, the signer. -/
def sealAt (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot) (command : Command)
    (ingress : DecodedIngress) : Seal :=
  ⟨authority.readGuards, [nullifier deployment.domain profile.semantics command],
    event deployment.domain profile.semantics ingress, some command.subject, charge ingress⟩

/-- This receiver's sealing on the kernel turn (`sealAt` its authority). -/
def admissionSeal (prepared : Prepared deployment profile ambient durable command) (ingress : DecodedIngress) : Seal :=
  sealAt (profile := profile) prepared.authority command ingress

/-- The refusals of a call tree that arise while it runs (after the root's front-end replay):
every one but a kernel refusal decided cheaply and an absent object. -/
def callAfterWork : ObjectiveCall.CallRefusal → Bool
  | .extractionAccount reason _ _ => callAfterWork reason
  | .extractionAllowanceExhausted | .extractionFailed _ => true
  | .kernel reason => reason.afterWork
  | .notAnObject _ => false
  | .reentry _ _ | .depth _ | .stateMissing _ | .notCallable _ _ _ | .notDeliverable _ _ _ | .continuationDepth _
  | .fanOut _ | .allowanceExceeded _ _ | .messageWide _ | .argumentType _ _ | .callShape _ _ _ | .frameFault _ _ _
  | .resultType _ _ | .grantSpent _ _ | .grantMismatch _ _ _ | .notControllable _ | .notSender _ _ | .slotInbox _ _
  | .lawDenied _ _ _ | .exhausted | .queueFull _ _ | .slotQueueFull _ | .notPipelinable _ | .slotTaken _
  | .inboxCodec _ _ | .packageCell _ | .drainConflict _
  -- the turn's front-end meter, drawn as frames load and sends are checked (GPT-6 row E)
  | .frontEndExhausted _ _ _ | .postageFrontEnd _ _ _ _ => true

/-- **The refusals a signed, authorized, funded turn is CHARGED for**: the ones it meets after
the validator's work (`ObjectiveActivity.Refusal.afterWork`, a call tree's own, the seat end),
and an outcome other than the signed one (`outcomeMoved`, a stale plan: like a revert's gas).
Every other refusal is decided cheaply and charges nothing. -/
def chargedCause : Reject → Bool
  | .kernel reason => reason.afterWork
  | .call reason _ => callAfterWork reason
  | .seats _ => true
  | .outcomeMoved _ _ => true
  -- decided before anything runs (decoding, authority, capabilities, the signature)
  | .malformedIngress | .directoryUnavailable | .authorityUnavailable | .staleAuthority | .replayedMarker
  | .physicalPreparation | .inputUndecodable | .staleAwait | .notObjectHolder | .notAccountOwner | .signature _ => false
  -- a message delivery is not yet a paying turn (`failureRequest`; cv 01a11680-f2a6)
  | .message _ => false

/-! ### Canonical terminal-failure record

The durable protocol's event is the record-shape extension point for this
receiver.  A charged failure must retain its typed `Reject`, not merely a
rendering, so replay can return the exact original terminal disposition. -/

/-- Empty constructor payload; constructor identity is supplied by the sum tag. -/
private def unitStream : StreamCodec Unit where
  encode _ := []
  decodePrefix suffix := some ((), suffix)
  decodePrefix_encode := by intro value suffix; cases value; rfl

private def uint32Stream : StreamCodec UInt32 :=
  StreamCodec.xmap StreamCodec.nat UInt32.toNat UInt32.ofNat
    (by intro value; simp)

private def stageStream : StreamCodec (ObjectiveWorkAccount.Stage) :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      unitStream))
      (StreamCodec.sum (StreamCodec.sum unitStream
      unitStream)
      (StreamCodec.sum unitStream
      unitStream)))
    (fun value => match value with
      | .frontEnd => (.inl (.inl ()))
      | .core => (.inl (.inr (.inl ())))
      | .check => (.inl (.inr (.inr ())))
      | .execution => (.inr (.inl (.inl ())))
      | .extraction => (.inr (.inl (.inr ())))
      | .output => (.inr (.inr (.inl ())))
      | .domain => (.inr (.inr (.inr ())))
    )
    (fun wire => match wire with
      | (.inl (.inl ())) => .frontEnd
      | (.inl (.inr (.inl ()))) => .core
      | (.inl (.inr (.inr ()))) => .check
      | (.inr (.inl (.inl ()))) => .execution
      | (.inr (.inl (.inr ()))) => .extraction
      | (.inr (.inr (.inl ()))) => .output
      | (.inr (.inr (.inr ()))) => .domain
    )
    (by intro value; cases value <;> rfl)

private def slotRefusalStream : StreamCodec (AnswerSlot.Refusal) :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
      (StreamCodec.sum (StreamCodec.product StreamCodec.nat StreamCodec.nat)
      (StreamCodec.sum unitStream
      unitStream)))
    (fun value => match value with
      | .notOpen => (.inl (.inl ()))
      | .notDecider => (.inl (.inr (.inl ())))
      | .pastDeadline deadline height => (.inl (.inr (.inr (deadline, height))))
      | .notYetExpired deadline height => (.inr (.inl (deadline, height)))
      | .expiryIsKernelOnly => (.inr (.inr (.inl ())))
      | .deliveryDecides => (.inr (.inr (.inr ())))
    )
    (fun wire => match wire with
      | (.inl (.inl ())) => .notOpen
      | (.inl (.inr (.inl ()))) => .notDecider
      | (.inl (.inr (.inr (deadline, height)))) => .pastDeadline deadline height
      | (.inr (.inl (deadline, height))) => .notYetExpired deadline height
      | (.inr (.inr (.inl ()))) => .expiryIsKernelOnly
      | (.inr (.inr (.inr ()))) => .deliveryDecides
    )
    (by intro value; cases value <;> rfl)

private def grantFieldStream : StreamCodec (ObjectiveCall.GrantField) :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.sum unitStream
      unitStream)
      (StreamCodec.sum unitStream
      unitStream))
    (fun value => match value with
      | .code => (.inl (.inl ()))
      | .caller => (.inl (.inr ()))
      | .args => (.inr (.inl ()))
      | .cap => (.inr (.inr ()))
    )
    (fun wire => match wire with
      | (.inl (.inl ())) => .code
      | (.inl (.inr ())) => .caller
      | (.inr (.inl ())) => .args
      | (.inr (.inr ())) => .cap
    )
    (by intro value; cases value <;> rfl)

/-- Store recursive upgrade-conflict depth beside its typed terminal. -/
private def splitWriteRefusal : ObjectRecord.WriteRefusal →
    Nat × (Sum Unit (Sum Unit (Sum LawLeaf Unit)))
  | .illTyped => (0, .inl ())
  | .unprojectable => (0, .inr (.inl ()))
  | .lawDenied leaf => (0, .inr (.inr (.inl leaf)))
  | .unmigrated => (0, .inr (.inr (.inr ())))
  | .upgradeConflict reason =>
      let (depth, terminal) := splitWriteRefusal reason
      (depth + 1, terminal)

private def joinWriteRefusal (depth : Nat)
    (terminal : Sum Unit (Sum Unit (Sum LawLeaf Unit))) : ObjectRecord.WriteRefusal :=
  match depth with
  | 0 => match terminal with
    | .inl _ => .illTyped
    | .inr (.inl _) => .unprojectable
    | .inr (.inr (.inl leaf)) => .lawDenied leaf
    | .inr (.inr (.inr _)) => .unmigrated
  | depth + 1 => .upgradeConflict (joinWriteRefusal depth terminal)

private theorem join_split_writeRefusal (reason : ObjectRecord.WriteRefusal) :
    joinWriteRefusal (splitWriteRefusal reason).1 (splitWriteRefusal reason).2 = reason := by
  induction reason with
  | upgradeConflict reason ih =>
      simp only [splitWriteRefusal]
      cases found : splitWriteRefusal reason with
      | mk depth terminal =>
          rw [found] at ih
          exact congrArg ObjectRecord.WriteRefusal.upgradeConflict ih
  | _ => rfl

private def writeRefusalStream : StreamCodec ObjectRecord.WriteRefusal :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.sum unitStream (StreamCodec.sum unitStream (StreamCodec.sum LawLeaf.stream unitStream))))
    splitWriteRefusal (fun wire => joinWriteRefusal wire.1 wire.2) join_split_writeRefusal

private def invitationRefusalStream : StreamCodec (Invitations.Refusal) :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.sum StreamCodec.nat
      (StreamCodec.sum StreamCodec.nat
      unitStream))
      (StreamCodec.sum (StreamCodec.sum StreamCodec.nat
      StreamCodec.nat)
      (StreamCodec.sum StreamCodec.nat
      StreamCodec.nat)))
    (fun value => match value with
      | .instanceMissing inst => (.inl (.inl inst))
      | .notTheInstance inst => (.inl (.inr (.inl inst)))
      | .packageMismatch => (.inl (.inr (.inr ())))
      | .idUsed entryId => (.inr (.inl (.inl entryId)))
      | .invitationMissing entryId => (.inr (.inl (.inr entryId)))
      | .notHolder entryId => (.inr (.inr (.inl entryId)))
      | .assayFailed entryId => (.inr (.inr (.inr entryId)))
    )
    (fun wire => match wire with
      | (.inl (.inl inst)) => .instanceMissing inst
      | (.inl (.inr (.inl inst))) => .notTheInstance inst
      | (.inl (.inr (.inr ()))) => .packageMismatch
      | (.inr (.inl (.inl entryId))) => .idUsed entryId
      | (.inr (.inl (.inr entryId))) => .invitationMissing entryId
      | (.inr (.inr (.inl entryId))) => .notHolder entryId
      | (.inr (.inr (.inr entryId))) => .assayFailed entryId
    )
    (by intro value; cases value <;> rfl)

private def bookRefusalStream : StreamCodec (Seats.BookRefusal) :=
  StreamCodec.xmap
    (StreamCodec.sum StreamCodec.nat
      (StreamCodec.sum StreamCodec.nat
      (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
    (fun value => match value with
      | .accountNotFresh account => (.inl account)
      | .missing account => (.inr (.inl account))
      | .unfunded account asset => (.inr (.inr (account, asset)))
    )
    (fun wire => match wire with
      | (.inl account) => .accountNotFresh account
      | (.inr (.inl account)) => .missing account
      | (.inr (.inr (account, asset))) => .unfunded account asset
    )
    (by intro value; cases value <;> rfl)

private def transferStream : StreamCodec Seats.Transfer :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
    (fun value => (value.source, value.destination, value.asset, value.amount))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro value; cases value; rfl)

private def seatRefusalStream : StreamCodec (Seats.Refusal) :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum invitationRefusalStream
      unitStream)
      (StreamCodec.sum unitStream
      StreamCodec.nat))
      (StreamCodec.sum (StreamCodec.sum StreamCodec.nat
      StreamCodec.nat)
      (StreamCodec.sum StreamCodec.nat
      (StreamCodec.sum StreamCodec.nat
      bookRefusalStream))))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum StreamCodec.nat
      (StreamCodec.product transferStream StreamCodec.nat))
      (StreamCodec.sum StreamCodec.nat
      StreamCodec.nat))
      (StreamCodec.sum (StreamCodec.sum StreamCodec.nat
      StreamCodec.nat)
      (StreamCodec.sum StreamCodec.nat
      (StreamCodec.sum StreamCodec.nat
      StreamCodec.nat)))))
    (fun value => match value with
      | .invitation reason => (.inl (.inl (.inl (.inl reason))))
      | .notASubject => (.inl (.inl (.inl (.inr ()))))
      | .notAnInstance => (.inl (.inl (.inr (.inl ()))))
      | .notTheInstance inst => (.inl (.inl (.inr (.inr inst))))
      | .seatNotProtected account => (.inl (.inr (.inl (.inl account))))
      | .fundingProtected account => (.inl (.inr (.inl (.inr account))))
      | .payeeProtected account => (.inl (.inr (.inr (.inl account))))
      | .payeeMissing account => (.inl (.inr (.inr (.inr (.inl account)))))
      | .book reason => (.inl (.inr (.inr (.inr (.inr reason)))))
      | .offerUnsafe account => (.inr (.inl (.inl (.inl account))))
      | .outsideSeats transfer inst => (.inr (.inl (.inl (.inr (transfer, inst)))))
      | .contractClauseRefused inst => (.inr (.inl (.inr (.inl inst))))
      | .seatMissing account => (.inr (.inl (.inr (.inr account))))
      | .seatLeased account => (.inr (.inr (.inl (.inl account))))
      | .donationUnmarked account => (.inr (.inr (.inl (.inr account))))
      | .donationMarkedWithWant account => (.inr (.inr (.inr (.inl account))))
      | .exitNotAuthorized account => (.inr (.inr (.inr (.inr (.inl account)))))
      | .instanceExists inst => (.inr (.inr (.inr (.inr (.inr inst)))))
    )
    (fun wire => match wire with
      | (.inl (.inl (.inl (.inl reason)))) => .invitation reason
      | (.inl (.inl (.inl (.inr ())))) => .notASubject
      | (.inl (.inl (.inr (.inl ())))) => .notAnInstance
      | (.inl (.inl (.inr (.inr inst)))) => .notTheInstance inst
      | (.inl (.inr (.inl (.inl account)))) => .seatNotProtected account
      | (.inl (.inr (.inl (.inr account)))) => .fundingProtected account
      | (.inl (.inr (.inr (.inl account)))) => .payeeProtected account
      | (.inl (.inr (.inr (.inr (.inl account))))) => .payeeMissing account
      | (.inl (.inr (.inr (.inr (.inr reason))))) => .book reason
      | (.inr (.inl (.inl (.inl account)))) => .offerUnsafe account
      | (.inr (.inl (.inl (.inr (transfer, inst))))) => .outsideSeats transfer inst
      | (.inr (.inl (.inr (.inl inst)))) => .contractClauseRefused inst
      | (.inr (.inl (.inr (.inr account)))) => .seatMissing account
      | (.inr (.inr (.inl (.inl account)))) => .seatLeased account
      | (.inr (.inr (.inl (.inr account)))) => .donationUnmarked account
      | (.inr (.inr (.inr (.inl account)))) => .donationMarkedWithWant account
      | (.inr (.inr (.inr (.inr (.inl account))))) => .exitNotAuthorized account
      | (.inr (.inr (.inr (.inr (.inr inst))))) => .instanceExists inst
    )
    (by intro value; cases value <;> rfl)

/-- Extend a binary constructor root with tag 2. Tags 0 and 1 retain
exactly the original sum bytes, including every nested constructor payload. -/
private def sumWithStateRetired {A B : Type} (left : StreamCodec A) (right : StreamCodec B) :
    StreamCodec (Sum (Sum A B) Unit) where
  encode
    | .inl (.inl value) => 0 :: left.encode value
    | .inl (.inr value) => 1 :: right.encode value
    | .inr _ => [2]
  decodePrefix
    | 0 :: bytes => do
        let (value, suffix) ← left.decodePrefix bytes
        some (.inl (.inl value), suffix)
    | 1 :: bytes => do
        let (value, suffix) ← right.decodePrefix bytes
        some (.inl (.inr value), suffix)
    | 2 :: suffix => some (.inr (), suffix)
    | _ => none
  decodePrefix_encode := by
    intro value suffix
    cases value with
    | inl value => cases value <;> simp [left.decodePrefix_encode, right.decodePrefix_encode]
    | inr value => cases value; rfl

private theorem sumWithStateRetired_existing {A B : Type}
    (left : StreamCodec A) (right : StreamCodec B) (value : Sum A B) :
    (sumWithStateRetired left right).encode (.inl value) =
      (StreamCodec.sum left right).encode value := by
  cases value <;> rfl

private def activityRefusalStream : StreamCodec (ObjectiveActivity.Refusal) :=
  StreamCodec.xmap
    (sumWithStateRetired (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum unitStream
      unitStream)
      (StreamCodec.sum stringStream
      (StreamCodec.sum unitStream
      stringStream)))
      (StreamCodec.sum (StreamCodec.sum stringStream
      (StreamCodec.sum unitStream
      stringStream))
      (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      unitStream))))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum unitStream
      unitStream)
      (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      unitStream)))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.product StreamCodec.nat StreamCodec.nat)
      (StreamCodec.sum (StreamCodec.product digestStream digestStream)
      (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
      (StreamCodec.sum capacityStream
      (StreamCodec.sum (StreamCodec.product StreamCodec.nat StreamCodec.nat)
      (StreamCodec.product StreamCodec.nat StreamCodec.nat))))))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.product stageStream (StreamCodec.product StreamCodec.nat StreamCodec.nat))
      (StreamCodec.product IntStream.intStream StreamCodec.nat))
      (StreamCodec.sum stringStream
      (StreamCodec.sum unitStream
      stringStream)))
      (StreamCodec.sum (StreamCodec.sum stringStream
      (StreamCodec.sum unitStream
      stringStream))
      (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      unitStream))))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum slotRefusalStream
      (StreamCodec.sum unitStream
      (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
      (StreamCodec.sum (StreamCodec.product StreamCodec.nat StreamCodec.nat)
      (StreamCodec.sum unitStream
      unitStream)))
      (StreamCodec.sum (StreamCodec.sum unitStream
      (StreamCodec.sum (StreamCodec.product StreamCodec.nat StreamCodec.nat)
      (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
      (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      unitStream))))))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum stringStream
      unitStream)
      (StreamCodec.sum unitStream
      (StreamCodec.sum (StreamCodec.product StreamCodec.nat StreamCodec.nat)
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))
      (StreamCodec.sum (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      unitStream))
      (StreamCodec.sum unitStream
      (StreamCodec.sum (StreamCodec.product digestStream digestStream)
      writeRefusalStream))))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      unitStream))
      (StreamCodec.sum stringStream
      (StreamCodec.sum unitStream
      unitStream)))
      (StreamCodec.sum (StreamCodec.sum stringStream
      (StreamCodec.sum stringStream
      unitStream))
      (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      StreamCodec.nat)))))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum unitStream
      unitStream)
      (StreamCodec.sum unitStream
      (StreamCodec.sum (StreamCodec.product StreamCodec.nat StreamCodec.nat)
      unitStream)))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.list stringStream)
      (StreamCodec.sum StreamCodec.nat
      (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
      (StreamCodec.sum unitStream
      (StreamCodec.sum stringStream
      (StreamCodec.product digestStream LawLeaf.stream)))))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum digestStream
      (StreamCodec.sum digestStream
      digestStream))
      (StreamCodec.sum digestStream
      (StreamCodec.sum stringStream
      StreamCodec.nat)))
      (StreamCodec.sum (StreamCodec.sum StreamCodec.nat
      (StreamCodec.sum StreamCodec.nat
      StreamCodec.nat))
      (StreamCodec.sum StreamCodec.nat
      (StreamCodec.sum (StreamCodec.product digestStream StreamCodec.nat)
      (StreamCodec.product StreamCodec.nat StreamCodec.nat))))))))
    (fun value => match value with
      | .stateRetired => .inr ()
      | .packageMissing => .inl (.inl (.inl (.inl (.inl (.inl (.inl ()))))))
      | .packageIdentity => .inl (.inl (.inl (.inl (.inl (.inl (.inr ()))))))
      | .packageType reason => .inl (.inl (.inl (.inl (.inl (.inr (.inl reason))))))
      | .packageExists => .inl (.inl (.inl (.inl (.inl (.inr (.inr (.inl ())))))))
      | .packageSource reason => .inl (.inl (.inl (.inl (.inl (.inr (.inr (.inr reason)))))))
      | .packageReplay reason => .inl (.inl (.inl (.inl (.inr (.inl (.inl reason))))))
      | .inputType => .inl (.inl (.inl (.inl (.inr (.inl (.inr (.inl ())))))))
      | .outcomeProtocol label => .inl (.inl (.inl (.inl (.inr (.inl (.inr (.inr label)))))))
      | .recordExists => .inl (.inl (.inl (.inl (.inr (.inr (.inl ()))))))
      | .recordMissing => .inl (.inl (.inl (.inl (.inr (.inr (.inr (.inl ())))))))
      | .recordMisplaced => .inl (.inl (.inl (.inl (.inr (.inr (.inr (.inr ())))))))
      | .notAwaiting => .inl (.inl (.inl (.inr (.inl (.inl (.inl ()))))))
      | .awaitMismatch => .inl (.inl (.inl (.inr (.inl (.inl (.inr ()))))))
      | .checkpointDigest => .inl (.inl (.inl (.inr (.inl (.inr (.inl ()))))))
      | .checkpointCodec => .inl (.inl (.inl (.inr (.inl (.inr (.inr (.inl ())))))))
      | .recordRetired => .inl (.inl (.inl (.inr (.inl (.inr (.inr (.inr ())))))))
      | .patience patience maximum => .inl (.inl (.inl (.inr (.inr (.inl (.inl (patience, maximum)))))))
      | .digestWide object pin => .inl (.inl (.inl (.inr (.inr (.inl (.inr (.inl (object, pin))))))))
      | .heightWide height patience => .inl (.inl (.inl (.inr (.inr (.inl (.inr (.inr (height, patience))))))))
      | .uncovered envelope => .inl (.inl (.inl (.inr (.inr (.inr (.inl envelope))))))
      | .heapUncovered needed declared => .inl (.inl (.inl (.inr (.inr (.inr (.inr (.inl (needed, declared))))))))
      | .extractUncovered needed declared => .inl (.inl (.inl (.inr (.inr (.inr (.inr (.inr (needed, declared))))))))
      | .workUncovered stage needed declared => .inl (.inl (.inr (.inl (.inl (.inl (.inl (stage, needed, declared)))))))
      | .unfunded available price => .inl (.inl (.inr (.inl (.inl (.inl (.inr (available, price)))))))
      | .plan reason => .inl (.inl (.inr (.inl (.inl (.inr (.inl reason))))))
      | .messageAwaitNeedsInbox => .inl (.inl (.inr (.inl (.inl (.inr (.inr (.inl ())))))))
      | .planExtraction reason => .inl (.inl (.inr (.inl (.inl (.inr (.inr (.inr reason)))))))
      | .resultExtraction reason => .inl (.inl (.inr (.inl (.inr (.inl (.inl reason))))))
      | .exhausted => .inl (.inl (.inr (.inl (.inr (.inl (.inr (.inl ())))))))
      | .responseType label => .inl (.inl (.inr (.inl (.inr (.inl (.inr (.inr label)))))))
      | .slotMissing => .inl (.inl (.inr (.inl (.inr (.inr (.inl ()))))))
      | .slotFresh => .inl (.inl (.inr (.inl (.inr (.inr (.inr (.inl ())))))))
      | .slotMismatch => .inl (.inl (.inr (.inl (.inr (.inr (.inr (.inr ())))))))
      | .slot reason => .inl (.inl (.inr (.inr (.inl (.inl (.inl reason))))))
      | .slotRetired => .inl (.inl (.inr (.inr (.inl (.inl (.inr (.inl ())))))))
      | .notYetDecided deadline height => .inl (.inl (.inr (.inr (.inl (.inl (.inr (.inr (deadline, height))))))))
      | .notYetDue due height => .inl (.inl (.inr (.inr (.inl (.inr (.inl (due, height)))))))
      | .bookUnavailable => .inl (.inl (.inr (.inr (.inl (.inr (.inr (.inl ())))))))
      | .purseTaken => .inl (.inl (.inr (.inr (.inl (.inr (.inr (.inr ())))))))
      | .payerInvalid => .inl (.inl (.inr (.inr (.inr (.inl (.inl ()))))))
      | .underfunded deposit reserve => .inl (.inl (.inr (.inr (.inr (.inl (.inr (.inl (deposit, reserve))))))))
      | .awaitsFunding available reserve => .inl (.inl (.inr (.inr (.inr (.inl (.inr (.inr (available, reserve))))))))
      | .bookRefused => .inl (.inl (.inr (.inr (.inr (.inr (.inl ()))))))
      | .zeroAmount => .inl (.inl (.inr (.inr (.inr (.inr (.inr (.inl ())))))))
      | .blindWrite => .inl (.inl (.inr (.inr (.inr (.inr (.inr (.inr ())))))))
      | .writeShape reason => .inl (.inr (.inl (.inl (.inl (.inl (.inl reason))))))
      | .stateCodec => .inl (.inr (.inl (.inl (.inl (.inl (.inr ()))))))
      | .stateMissing => .inl (.inr (.inl (.inl (.inl (.inr (.inl ()))))))
      | .alreadyExhausted tried envelope => .inl (.inr (.inl (.inl (.inl (.inr (.inr (.inl (tried, envelope))))))))
      | .notYetAbandonable deadline grace height => .inl (.inr (.inl (.inl (.inl (.inr (.inr (.inr (deadline, grace, height))))))))
      | .notExhausted => .inl (.inr (.inl (.inl (.inr (.inl (.inl ()))))))
      | .notAnObject => .inl (.inr (.inl (.inl (.inr (.inl (.inr (.inl ())))))))
      | .objectCodec => .inl (.inr (.inl (.inl (.inr (.inl (.inr (.inr ())))))))
      | .objectExists => .inl (.inr (.inl (.inl (.inr (.inr (.inl ()))))))
      | .pinMismatch pinned requested => .inl (.inr (.inl (.inl (.inr (.inr (.inr (.inl (pinned, requested))))))))
      | .objectWrite reason => .inl (.inr (.inl (.inl (.inr (.inr (.inr (.inr reason)))))))
      | .pinUnpublished => .inl (.inr (.inl (.inr (.inl (.inl (.inl ()))))))
      | .stateExists => .inl (.inr (.inl (.inr (.inl (.inl (.inr (.inl ())))))))
      | .stateTypeNotData => .inl (.inr (.inl (.inr (.inl (.inl (.inr (.inr ())))))))
      | .lawField field => .inl (.inr (.inl (.inr (.inl (.inr (.inl field))))))
      | .draining => .inl (.inr (.inl (.inr (.inl (.inr (.inr (.inl ())))))))
      | .awaitingRebirth => .inl (.inr (.inl (.inr (.inl (.inr (.inr (.inr ())))))))
      | .migrationShape reason => .inl (.inr (.inl (.inr (.inr (.inl (.inl reason))))))
      | .migrationFault reason => .inl (.inr (.inl (.inr (.inr (.inl (.inr (.inl reason)))))))
      | .frozen => .inl (.inr (.inl (.inr (.inr (.inl (.inr (.inr ())))))))
      | .notUpgradeAuthority => .inl (.inr (.inl (.inr (.inr (.inr (.inl ()))))))
      | .policyLoosened => .inl (.inr (.inl (.inr (.inr (.inr (.inr (.inl ())))))))
      | .floorNotEntailed index => .inl (.inr (.inl (.inr (.inr (.inr (.inr (.inr index)))))))
      | .samePin => .inl (.inr (.inr (.inl (.inl (.inl (.inl ()))))))
      | .upgradeUnderWay => .inl (.inr (.inr (.inl (.inl (.inl (.inr ()))))))
      | .notDraining => .inl (.inr (.inr (.inl (.inl (.inr (.inl ()))))))
      | .drainPatience patience maximum => .inl (.inr (.inr (.inl (.inl (.inr (.inr (.inl (patience, maximum))))))))
      | .notSubtype => .inl (.inr (.inr (.inl (.inl (.inr (.inr (.inr ())))))))
      | .fieldsForgotten fields => .inl (.inr (.inr (.inl (.inr (.inl (.inl fields))))))
      | .liveActivities count => .inl (.inr (.inr (.inl (.inr (.inl (.inr (.inl count)))))))
      | .notYetDeadline deadline height => .inl (.inr (.inr (.inl (.inr (.inl (.inr (.inr (deadline, height))))))))
      | .rebirthDisposition => .inl (.inr (.inr (.inl (.inr (.inr (.inl ()))))))
      | .rebirthTarget reason => .inl (.inr (.inr (.inl (.inr (.inr (.inr (.inl reason)))))))
      | .domainLawDenied domain leaf => .inl (.inr (.inr (.inl (.inr (.inr (.inr (.inr (domain, leaf))))))))
      | .domainUnprojectable domain => .inl (.inr (.inr (.inr (.inl (.inl (.inl domain))))))
      | .domainMissing domain => .inl (.inr (.inr (.inr (.inl (.inl (.inr (.inl domain)))))))
      | .domainCodec domain => .inl (.inr (.inr (.inr (.inl (.inl (.inr (.inr domain)))))))
      | .domainExists domain => .inl (.inr (.inr (.inr (.inl (.inr (.inl domain))))))
      | .domainShape reason => .inl (.inr (.inr (.inr (.inl (.inr (.inr (.inl reason)))))))
      | .domainMember object => .inl (.inr (.inr (.inr (.inl (.inr (.inr (.inr object)))))))
      | .memberFrozen object => .inl (.inr (.inr (.inr (.inr (.inl (.inl object))))))
      | .memberDenied object => .inl (.inr (.inr (.inr (.inr (.inl (.inr (.inl object)))))))
      | .memberDomainsFull object => .inl (.inr (.inr (.inr (.inr (.inl (.inr (.inr object)))))))
      | .domainsDropped object => .inl (.inr (.inr (.inr (.inr (.inr (.inl object))))))
      | .domainUnindexed domain member => .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inl (domain, member))))))))
      | .domainUncovered units allowance => .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (units, allowance))))))))
    )
    (fun wire => match wire with
      | .inr _ => .stateRetired
      | .inl wire => match wire with
        | (.inl (.inl (.inl (.inl (.inl (.inl ())))))) => .packageMissing
        | (.inl (.inl (.inl (.inl (.inl (.inr ())))))) => .packageIdentity
        | (.inl (.inl (.inl (.inl (.inr (.inl reason)))))) => .packageType reason
        | (.inl (.inl (.inl (.inl (.inr (.inr (.inl ()))))))) => .packageExists
        | (.inl (.inl (.inl (.inl (.inr (.inr (.inr reason))))))) => .packageSource reason
        | (.inl (.inl (.inl (.inr (.inl (.inl reason)))))) => .packageReplay reason
        | (.inl (.inl (.inl (.inr (.inl (.inr (.inl ()))))))) => .inputType
        | (.inl (.inl (.inl (.inr (.inl (.inr (.inr label))))))) => .outcomeProtocol label
        | (.inl (.inl (.inl (.inr (.inr (.inl ())))))) => .recordExists
        | (.inl (.inl (.inl (.inr (.inr (.inr (.inl ()))))))) => .recordMissing
        | (.inl (.inl (.inl (.inr (.inr (.inr (.inr ()))))))) => .recordMisplaced
        | (.inl (.inl (.inr (.inl (.inl (.inl ())))))) => .notAwaiting
        | (.inl (.inl (.inr (.inl (.inl (.inr ())))))) => .awaitMismatch
        | (.inl (.inl (.inr (.inl (.inr (.inl ())))))) => .checkpointDigest
        | (.inl (.inl (.inr (.inl (.inr (.inr (.inl ()))))))) => .checkpointCodec
        | (.inl (.inl (.inr (.inl (.inr (.inr (.inr ()))))))) => .recordRetired
        | (.inl (.inl (.inr (.inr (.inl (.inl (patience, maximum))))))) => .patience patience maximum
        | (.inl (.inl (.inr (.inr (.inl (.inr (.inl (object, pin)))))))) => .digestWide object pin
        | (.inl (.inl (.inr (.inr (.inl (.inr (.inr (height, patience)))))))) => .heightWide height patience
        | (.inl (.inl (.inr (.inr (.inr (.inl envelope)))))) => .uncovered envelope
        | (.inl (.inl (.inr (.inr (.inr (.inr (.inl (needed, declared)))))))) => .heapUncovered needed declared
        | (.inl (.inl (.inr (.inr (.inr (.inr (.inr (needed, declared)))))))) => .extractUncovered needed declared
        | (.inl (.inr (.inl (.inl (.inl (.inl (stage, needed, declared))))))) => .workUncovered stage needed declared
        | (.inl (.inr (.inl (.inl (.inl (.inr (available, price))))))) => .unfunded available price
        | (.inl (.inr (.inl (.inl (.inr (.inl reason)))))) => .plan reason
        | (.inl (.inr (.inl (.inl (.inr (.inr (.inl ()))))))) => .messageAwaitNeedsInbox
        | (.inl (.inr (.inl (.inl (.inr (.inr (.inr reason))))))) => .planExtraction reason
        | (.inl (.inr (.inl (.inr (.inl (.inl reason)))))) => .resultExtraction reason
        | (.inl (.inr (.inl (.inr (.inl (.inr (.inl ()))))))) => .exhausted
        | (.inl (.inr (.inl (.inr (.inl (.inr (.inr label))))))) => .responseType label
        | (.inl (.inr (.inl (.inr (.inr (.inl ())))))) => .slotMissing
        | (.inl (.inr (.inl (.inr (.inr (.inr (.inl ()))))))) => .slotFresh
        | (.inl (.inr (.inl (.inr (.inr (.inr (.inr ()))))))) => .slotMismatch
        | (.inl (.inr (.inr (.inl (.inl (.inl reason)))))) => .slot reason
        | (.inl (.inr (.inr (.inl (.inl (.inr (.inl ()))))))) => .slotRetired
        | (.inl (.inr (.inr (.inl (.inl (.inr (.inr (deadline, height)))))))) => .notYetDecided deadline height
        | (.inl (.inr (.inr (.inl (.inr (.inl (due, height))))))) => .notYetDue due height
        | (.inl (.inr (.inr (.inl (.inr (.inr (.inl ()))))))) => .bookUnavailable
        | (.inl (.inr (.inr (.inl (.inr (.inr (.inr ()))))))) => .purseTaken
        | (.inl (.inr (.inr (.inr (.inl (.inl ())))))) => .payerInvalid
        | (.inl (.inr (.inr (.inr (.inl (.inr (.inl (deposit, reserve)))))))) => .underfunded deposit reserve
        | (.inl (.inr (.inr (.inr (.inl (.inr (.inr (available, reserve)))))))) => .awaitsFunding available reserve
        | (.inl (.inr (.inr (.inr (.inr (.inl ())))))) => .bookRefused
        | (.inl (.inr (.inr (.inr (.inr (.inr (.inl ()))))))) => .zeroAmount
        | (.inl (.inr (.inr (.inr (.inr (.inr (.inr ()))))))) => .blindWrite
        | (.inr (.inl (.inl (.inl (.inl (.inl reason)))))) => .writeShape reason
        | (.inr (.inl (.inl (.inl (.inl (.inr ())))))) => .stateCodec
        | (.inr (.inl (.inl (.inl (.inr (.inl ())))))) => .stateMissing
        | (.inr (.inl (.inl (.inl (.inr (.inr (.inl (tried, envelope)))))))) => .alreadyExhausted tried envelope
        | (.inr (.inl (.inl (.inl (.inr (.inr (.inr (deadline, grace, height)))))))) => .notYetAbandonable deadline grace height
        | (.inr (.inl (.inl (.inr (.inl (.inl ())))))) => .notExhausted
        | (.inr (.inl (.inl (.inr (.inl (.inr (.inl ()))))))) => .notAnObject
        | (.inr (.inl (.inl (.inr (.inl (.inr (.inr ()))))))) => .objectCodec
        | (.inr (.inl (.inl (.inr (.inr (.inl ())))))) => .objectExists
        | (.inr (.inl (.inl (.inr (.inr (.inr (.inl (pinned, requested)))))))) => .pinMismatch pinned requested
        | (.inr (.inl (.inl (.inr (.inr (.inr (.inr reason))))))) => .objectWrite reason
        | (.inr (.inl (.inr (.inl (.inl (.inl ())))))) => .pinUnpublished
        | (.inr (.inl (.inr (.inl (.inl (.inr (.inl ()))))))) => .stateExists
        | (.inr (.inl (.inr (.inl (.inl (.inr (.inr ()))))))) => .stateTypeNotData
        | (.inr (.inl (.inr (.inl (.inr (.inl field)))))) => .lawField field
        | (.inr (.inl (.inr (.inl (.inr (.inr (.inl ()))))))) => .draining
        | (.inr (.inl (.inr (.inl (.inr (.inr (.inr ()))))))) => .awaitingRebirth
        | (.inr (.inl (.inr (.inr (.inl (.inl reason)))))) => .migrationShape reason
        | (.inr (.inl (.inr (.inr (.inl (.inr (.inl reason))))))) => .migrationFault reason
        | (.inr (.inl (.inr (.inr (.inl (.inr (.inr ()))))))) => .frozen
        | (.inr (.inl (.inr (.inr (.inr (.inl ())))))) => .notUpgradeAuthority
        | (.inr (.inl (.inr (.inr (.inr (.inr (.inl ()))))))) => .policyLoosened
        | (.inr (.inl (.inr (.inr (.inr (.inr (.inr index))))))) => .floorNotEntailed index
        | (.inr (.inr (.inl (.inl (.inl (.inl ())))))) => .samePin
        | (.inr (.inr (.inl (.inl (.inl (.inr ())))))) => .upgradeUnderWay
        | (.inr (.inr (.inl (.inl (.inr (.inl ())))))) => .notDraining
        | (.inr (.inr (.inl (.inl (.inr (.inr (.inl (patience, maximum)))))))) => .drainPatience patience maximum
        | (.inr (.inr (.inl (.inl (.inr (.inr (.inr ()))))))) => .notSubtype
        | (.inr (.inr (.inl (.inr (.inl (.inl fields)))))) => .fieldsForgotten fields
        | (.inr (.inr (.inl (.inr (.inl (.inr (.inl count))))))) => .liveActivities count
        | (.inr (.inr (.inl (.inr (.inl (.inr (.inr (deadline, height)))))))) => .notYetDeadline deadline height
        | (.inr (.inr (.inl (.inr (.inr (.inl ())))))) => .rebirthDisposition
        | (.inr (.inr (.inl (.inr (.inr (.inr (.inl reason))))))) => .rebirthTarget reason
        | (.inr (.inr (.inl (.inr (.inr (.inr (.inr (domain, leaf)))))))) => .domainLawDenied domain leaf
        | (.inr (.inr (.inr (.inl (.inl (.inl domain)))))) => .domainUnprojectable domain
        | (.inr (.inr (.inr (.inl (.inl (.inr (.inl domain))))))) => .domainMissing domain
        | (.inr (.inr (.inr (.inl (.inl (.inr (.inr domain))))))) => .domainCodec domain
        | (.inr (.inr (.inr (.inl (.inr (.inl domain)))))) => .domainExists domain
        | (.inr (.inr (.inr (.inl (.inr (.inr (.inl reason))))))) => .domainShape reason
        | (.inr (.inr (.inr (.inl (.inr (.inr (.inr object))))))) => .domainMember object
        | (.inr (.inr (.inr (.inr (.inl (.inl object)))))) => .memberFrozen object
        | (.inr (.inr (.inr (.inr (.inl (.inr (.inl object))))))) => .memberDenied object
        | (.inr (.inr (.inr (.inr (.inl (.inr (.inr object))))))) => .memberDomainsFull object
        | (.inr (.inr (.inr (.inr (.inr (.inl object)))))) => .domainsDropped object
        | (.inr (.inr (.inr (.inr (.inr (.inr (.inl (domain, member)))))))) => .domainUnindexed domain member
        | (.inr (.inr (.inr (.inr (.inr (.inr (.inr (units, allowance)))))))) => .domainUncovered units allowance
    )
    (by intro value; cases value <;> rfl)

private theorem activityRefusalStream_stateRetired_encode :
    activityRefusalStream.encode .stateRetired = [2] := rfl

private theorem activityRefusalStream_stateRetired_prefix (suffix : List UInt8) :
    activityRefusalStream.decodePrefix (2 :: suffix) = some (.stateRetired, suffix) := rfl

private def seatStoreRefusalStream : StreamCodec (SeatStore.Refusal) :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum seatRefusalStream
      activityRefusalStream)
      (StreamCodec.sum unitStream
      unitStream))
      (StreamCodec.sum (StreamCodec.sum stringStream
      StreamCodec.nat)
      (StreamCodec.sum StreamCodec.nat
      (StreamCodec.sum StreamCodec.nat
      StreamCodec.nat))))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum StreamCodec.nat
      unitStream)
      (StreamCodec.sum stringStream
      unitStream))
      (StreamCodec.sum (StreamCodec.sum stringStream
      capacityStream)
      (StreamCodec.sum StreamCodec.nat
      (StreamCodec.sum unitStream
      unitStream)))))
    (fun value => match value with
      | .kernel reason => (.inl (.inl (.inl (.inl reason))))
      | .program reason => (.inl (.inl (.inl (.inr reason))))
      | .packageMissing => (.inl (.inl (.inr (.inl ()))))
      | .packageExists => (.inl (.inl (.inr (.inr ()))))
      | .notAContract reason => (.inl (.inr (.inl (.inl reason))))
      | .instanceMissing inst => (.inl (.inr (.inl (.inr inst))))
      | .cellUndecodable cell => (.inl (.inr (.inr (.inl cell))))
      | .seatRetired account => (.inl (.inr (.inr (.inr (.inl account)))))
      | .seatExists account => (.inl (.inr (.inr (.inr (.inr account)))))
      | .activityCellInSeatSpace cell => (.inr (.inl (.inl (.inl cell))))
      | .inputUndecodable => (.inr (.inl (.inl (.inr ()))))
      | .plan reason => (.inr (.inl (.inr (.inl reason))))
      | .methodYielded => (.inr (.inl (.inr (.inr ()))))
      | .methodFaulted reason => (.inr (.inr (.inl (.inl reason))))
      | .uncovered envelope => (.inr (.inr (.inl (.inr envelope))))
      | .payerInvalid account => (.inr (.inr (.inr (.inl account))))
      | .bookUnavailable => (.inr (.inr (.inr (.inr (.inl ())))))
      | .bookRefused => (.inr (.inr (.inr (.inr (.inr ())))))
    )
    (fun wire => match wire with
      | (.inl (.inl (.inl (.inl reason)))) => .kernel reason
      | (.inl (.inl (.inl (.inr reason)))) => .program reason
      | (.inl (.inl (.inr (.inl ())))) => .packageMissing
      | (.inl (.inl (.inr (.inr ())))) => .packageExists
      | (.inl (.inr (.inl (.inl reason)))) => .notAContract reason
      | (.inl (.inr (.inl (.inr inst)))) => .instanceMissing inst
      | (.inl (.inr (.inr (.inl cell)))) => .cellUndecodable cell
      | (.inl (.inr (.inr (.inr (.inl account))))) => .seatRetired account
      | (.inl (.inr (.inr (.inr (.inr account))))) => .seatExists account
      | (.inr (.inl (.inl (.inl cell)))) => .activityCellInSeatSpace cell
      | (.inr (.inl (.inl (.inr ())))) => .inputUndecodable
      | (.inr (.inl (.inr (.inl reason)))) => .plan reason
      | (.inr (.inl (.inr (.inr ())))) => .methodYielded
      | (.inr (.inr (.inl (.inl reason)))) => .methodFaulted reason
      | (.inr (.inr (.inl (.inr envelope)))) => .uncovered envelope
      | (.inr (.inr (.inr (.inl account)))) => .payerInvalid account
      | (.inr (.inr (.inr (.inr (.inl ()))))) => .bookUnavailable
      | (.inr (.inr (.inr (.inr (.inr ()))))) => .bookRefused
    )
    (by intro value; cases value <;> rfl)

/-- The non-recursive end of a call refusal.  `CallRefusal` itself is recursive only
because an invocation may attach one or more extraction-account layers to the
typed refusal that stopped its call tree.  Keeping the terminal separate for the
encoding avoids asking the generic deriving proof to normalize the large recursive
sum. -/
inductive CallRefusalTerminal where
  | extractionAllowanceExhausted
  | extractionFailed (reason : String)
  | kernel (reason : ObjectiveActivity.Refusal)
  | reentry (target : Nat) (stack : List Nat)
  | depth (limit : Nat)
  | notAnObject (target : Nat)
  | frontEndExhausted (stage : ObjectiveWorkAccount.Stage) (needed left : Nat)
  | postageFrontEnd (target : Nat) (stage : ObjectiveWorkAccount.Stage) (needed declared : Nat)
  | stateMissing (target : Nat)
  | notCallable (target : Nat) (method : String) (reason : String)
  | notDeliverable (target : Nat) (method : String) (reason : String)
  | continuationDepth (limit : Nat)
  | fanOut (limit : Nat)
  | allowanceExceeded (needed held : Nat)
  | messageWide (entryId : Nat)
  | argumentType (target : Nat) (method : String)
  | callShape (target : Nat) (method : String) (reason : String)
  | frameFault (target : Nat) (method : String) (reason : String)
  | resultType (caller : Nat) (method : String)
  | grantSpent (target : Nat) (method : String)
  | grantMismatch (target : Nat) (method : String) (field : ObjectiveCall.GrantField)
  | notControllable (slot : Nat)
  | notSender (slot sender : Nat)
  | slotInbox (slot : Nat) (reason : String)
  | lawDenied (target : Nat) (method : String) (reason : ObjectRecord.WriteRefusal)
  | exhausted
  | queueFull (sender target : Nat)
  | slotQueueFull (slot : Nat)
  | notPipelinable (slot : Nat)
  | slotTaken (slot : Nat)
  | inboxCodec (sender target : Nat)
  | packageCell (cell : Nat)
  | drainConflict (target : Nat)

private def CallRefusalTerminal.refusal : CallRefusalTerminal → ObjectiveCall.CallRefusal
  | .extractionAllowanceExhausted => .extractionAllowanceExhausted
  | .extractionFailed reason => .extractionFailed reason
  | .kernel reason => .kernel reason
  | .reentry target stack => .reentry target stack
  | .depth limit => .depth limit
  | .notAnObject target => .notAnObject target
  | .frontEndExhausted stage needed left => .frontEndExhausted stage needed left
  | .postageFrontEnd target stage needed declared => .postageFrontEnd target stage needed declared
  | .stateMissing target => .stateMissing target
  | .notCallable target method reason => .notCallable target method reason
  | .notDeliverable target method reason => .notDeliverable target method reason
  | .continuationDepth limit => .continuationDepth limit
  | .fanOut limit => .fanOut limit
  | .allowanceExceeded needed held => .allowanceExceeded needed held
  | .messageWide identifier => .messageWide identifier
  | .argumentType target method => .argumentType target method
  | .callShape target method reason => .callShape target method reason
  | .frameFault target method reason => .frameFault target method reason
  | .resultType caller method => .resultType caller method
  | .grantSpent target method => .grantSpent target method
  | .grantMismatch target method field => .grantMismatch target method field
  | .notControllable slot => .notControllable slot
  | .notSender slot sender => .notSender slot sender
  | .slotInbox slot reason => .slotInbox slot reason
  | .lawDenied target method reason => .lawDenied target method reason
  | .exhausted => .exhausted
  | .queueFull sender target => .queueFull sender target
  | .slotQueueFull slot => .slotQueueFull slot
  | .notPipelinable slot => .notPipelinable slot
  | .slotTaken slot => .slotTaken slot
  | .inboxCodec sender target => .inboxCodec sender target
  | .packageCell cell => .packageCell cell
  | .drainConflict target => .drainConflict target

/-- Normalize the sole recursive constructor into an outer-to-inner list of
`(remaining, spent)` extraction accounts and a non-recursive terminal. -/
private def splitCallRefusal : ObjectiveCall.CallRefusal →
    List (Nat × Nat) × CallRefusalTerminal
  | .extractionAccount reason remaining spent =>
      let (accounts, terminal) := splitCallRefusal reason
      ((remaining, spent) :: accounts, terminal)
  | .extractionAllowanceExhausted => ([], .extractionAllowanceExhausted)
  | .extractionFailed reason => ([], .extractionFailed reason)
  | .kernel reason => ([], .kernel reason)
  | .reentry target stack => ([], .reentry target stack)
  | .depth limit => ([], .depth limit)
  | .notAnObject target => ([], .notAnObject target)
  | .frontEndExhausted stage needed left => ([], .frontEndExhausted stage needed left)
  | .postageFrontEnd target stage needed declared => ([], .postageFrontEnd target stage needed declared)
  | .stateMissing target => ([], .stateMissing target)
  | .notCallable target method reason => ([], .notCallable target method reason)
  | .notDeliverable target method reason => ([], .notDeliverable target method reason)
  | .continuationDepth limit => ([], .continuationDepth limit)
  | .fanOut limit => ([], .fanOut limit)
  | .allowanceExceeded needed held => ([], .allowanceExceeded needed held)
  | .messageWide identifier => ([], .messageWide identifier)
  | .argumentType target method => ([], .argumentType target method)
  | .callShape target method reason => ([], .callShape target method reason)
  | .frameFault target method reason => ([], .frameFault target method reason)
  | .resultType caller method => ([], .resultType caller method)
  | .grantSpent target method => ([], .grantSpent target method)
  | .grantMismatch target method field => ([], .grantMismatch target method field)
  | .notControllable slot => ([], .notControllable slot)
  | .notSender slot sender => ([], .notSender slot sender)
  | .slotInbox slot reason => ([], .slotInbox slot reason)
  | .lawDenied target method reason => ([], .lawDenied target method reason)
  | .exhausted => ([], .exhausted)
  | .queueFull sender target => ([], .queueFull sender target)
  | .slotQueueFull slot => ([], .slotQueueFull slot)
  | .notPipelinable slot => ([], .notPipelinable slot)
  | .slotTaken slot => ([], .slotTaken slot)
  | .inboxCodec sender target => ([], .inboxCodec sender target)
  | .packageCell cell => ([], .packageCell cell)
  | .drainConflict target => ([], .drainConflict target)

private def joinCallRefusal : List (Nat × Nat) × CallRefusalTerminal →
    ObjectiveCall.CallRefusal
  | (accounts, terminal) => accounts.foldr
      (fun (remaining, spent) reason => .extractionAccount reason remaining spent)
      terminal.refusal

/-- The explicit refusal representation retains the exact typed terminal and
every extraction-account layer. -/
private theorem join_split_callRefusal (reason : ObjectiveCall.CallRefusal) :
    joinCallRefusal (splitCallRefusal reason) = reason := by
  induction reason <;> try rfl
  case extractionAccount reason remaining spent ih =>
      simp only [splitCallRefusal]
      cases split : splitCallRefusal reason with
      | mk accounts terminal =>
          rw [split] at ih
          change ObjectiveCall.CallRefusal.extractionAccount
            (joinCallRefusal (accounts, terminal)) remaining spent =
              ObjectiveCall.CallRefusal.extractionAccount reason remaining spent
          rw [ih]

private def callRefusalTerminalStream : StreamCodec (CallRefusalTerminal) :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum unitStream
      stringStream)
      (StreamCodec.sum activityRefusalStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.list StreamCodec.nat))))
      (StreamCodec.sum (StreamCodec.sum StreamCodec.nat
      StreamCodec.nat)
      (StreamCodec.sum (StreamCodec.product stageStream (StreamCodec.product StreamCodec.nat StreamCodec.nat))
      (StreamCodec.product StreamCodec.nat (StreamCodec.product stageStream (StreamCodec.product StreamCodec.nat StreamCodec.nat))))))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product stringStream stringStream)))
      (StreamCodec.sum (StreamCodec.product StreamCodec.nat (StreamCodec.product stringStream stringStream))
      StreamCodec.nat))
      (StreamCodec.sum (StreamCodec.sum StreamCodec.nat
      (StreamCodec.product StreamCodec.nat StreamCodec.nat))
      (StreamCodec.sum StreamCodec.nat
      (StreamCodec.product StreamCodec.nat stringStream)))))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.product StreamCodec.nat (StreamCodec.product stringStream stringStream))
      (StreamCodec.product StreamCodec.nat (StreamCodec.product stringStream stringStream)))
      (StreamCodec.sum (StreamCodec.product StreamCodec.nat stringStream)
      (StreamCodec.product StreamCodec.nat stringStream)))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.product StreamCodec.nat (StreamCodec.product stringStream grantFieldStream))
      StreamCodec.nat)
      (StreamCodec.sum (StreamCodec.product StreamCodec.nat StreamCodec.nat)
      (StreamCodec.product StreamCodec.nat stringStream))))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.product StreamCodec.nat (StreamCodec.product stringStream writeRefusalStream))
      unitStream)
      (StreamCodec.sum (StreamCodec.product StreamCodec.nat StreamCodec.nat)
      StreamCodec.nat))
      (StreamCodec.sum (StreamCodec.sum StreamCodec.nat
      StreamCodec.nat)
      (StreamCodec.sum (StreamCodec.product StreamCodec.nat StreamCodec.nat)
      (StreamCodec.sum StreamCodec.nat
      StreamCodec.nat))))))
    (fun value => match value with
      | .extractionAllowanceExhausted => (.inl (.inl (.inl (.inl (.inl ())))))
      | .extractionFailed reason => (.inl (.inl (.inl (.inl (.inr reason)))))
      | .kernel reason => (.inl (.inl (.inl (.inr (.inl reason)))))
      | .reentry target stack => (.inl (.inl (.inl (.inr (.inr (target, stack))))))
      | .depth limit => (.inl (.inl (.inr (.inl (.inl limit)))))
      | .notAnObject target => (.inl (.inl (.inr (.inl (.inr target)))))
      | .frontEndExhausted stage needed left => (.inl (.inl (.inr (.inr (.inl (stage, needed, left))))))
      | .postageFrontEnd target stage needed declared => (.inl (.inl (.inr (.inr (.inr (target, stage, needed, declared))))))
      | .stateMissing target => (.inl (.inr (.inl (.inl (.inl target)))))
      | .notCallable target method reason => (.inl (.inr (.inl (.inl (.inr (target, method, reason))))))
      | .notDeliverable target method reason => (.inl (.inr (.inl (.inr (.inl (target, method, reason))))))
      | .continuationDepth limit => (.inl (.inr (.inl (.inr (.inr limit)))))
      | .fanOut limit => (.inl (.inr (.inr (.inl (.inl limit)))))
      | .allowanceExceeded needed held => (.inl (.inr (.inr (.inl (.inr (needed, held))))))
      | .messageWide entryId => (.inl (.inr (.inr (.inr (.inl entryId)))))
      | .argumentType target method => (.inl (.inr (.inr (.inr (.inr (target, method))))))
      | .callShape target method reason => (.inr (.inl (.inl (.inl (.inl (target, method, reason))))))
      | .frameFault target method reason => (.inr (.inl (.inl (.inl (.inr (target, method, reason))))))
      | .resultType caller method => (.inr (.inl (.inl (.inr (.inl (caller, method))))))
      | .grantSpent target method => (.inr (.inl (.inl (.inr (.inr (target, method))))))
      | .grantMismatch target method field => (.inr (.inl (.inr (.inl (.inl (target, method, field))))))
      | .notControllable slot => (.inr (.inl (.inr (.inl (.inr slot)))))
      | .notSender slot sender => (.inr (.inl (.inr (.inr (.inl (slot, sender))))))
      | .slotInbox slot reason => (.inr (.inl (.inr (.inr (.inr (slot, reason))))))
      | .lawDenied target method reason => (.inr (.inr (.inl (.inl (.inl (target, method, reason))))))
      | .exhausted => (.inr (.inr (.inl (.inl (.inr ())))))
      | .queueFull sender target => (.inr (.inr (.inl (.inr (.inl (sender, target))))))
      | .slotQueueFull slot => (.inr (.inr (.inl (.inr (.inr slot)))))
      | .notPipelinable slot => (.inr (.inr (.inr (.inl (.inl slot)))))
      | .slotTaken slot => (.inr (.inr (.inr (.inl (.inr slot)))))
      | .inboxCodec sender target => (.inr (.inr (.inr (.inr (.inl (sender, target))))))
      | .packageCell cell => (.inr (.inr (.inr (.inr (.inr (.inl cell))))))
      | .drainConflict target => (.inr (.inr (.inr (.inr (.inr (.inr target))))))
    )
    (fun wire => match wire with
      | (.inl (.inl (.inl (.inl (.inl ()))))) => .extractionAllowanceExhausted
      | (.inl (.inl (.inl (.inl (.inr reason))))) => .extractionFailed reason
      | (.inl (.inl (.inl (.inr (.inl reason))))) => .kernel reason
      | (.inl (.inl (.inl (.inr (.inr (target, stack)))))) => .reentry target stack
      | (.inl (.inl (.inr (.inl (.inl limit))))) => .depth limit
      | (.inl (.inl (.inr (.inl (.inr target))))) => .notAnObject target
      | (.inl (.inl (.inr (.inr (.inl (stage, needed, left)))))) => .frontEndExhausted stage needed left
      | (.inl (.inl (.inr (.inr (.inr (target, stage, needed, declared)))))) => .postageFrontEnd target stage needed declared
      | (.inl (.inr (.inl (.inl (.inl target))))) => .stateMissing target
      | (.inl (.inr (.inl (.inl (.inr (target, method, reason)))))) => .notCallable target method reason
      | (.inl (.inr (.inl (.inr (.inl (target, method, reason)))))) => .notDeliverable target method reason
      | (.inl (.inr (.inl (.inr (.inr limit))))) => .continuationDepth limit
      | (.inl (.inr (.inr (.inl (.inl limit))))) => .fanOut limit
      | (.inl (.inr (.inr (.inl (.inr (needed, held)))))) => .allowanceExceeded needed held
      | (.inl (.inr (.inr (.inr (.inl entryId))))) => .messageWide entryId
      | (.inl (.inr (.inr (.inr (.inr (target, method)))))) => .argumentType target method
      | (.inr (.inl (.inl (.inl (.inl (target, method, reason)))))) => .callShape target method reason
      | (.inr (.inl (.inl (.inl (.inr (target, method, reason)))))) => .frameFault target method reason
      | (.inr (.inl (.inl (.inr (.inl (caller, method)))))) => .resultType caller method
      | (.inr (.inl (.inl (.inr (.inr (target, method)))))) => .grantSpent target method
      | (.inr (.inl (.inr (.inl (.inl (target, method, field)))))) => .grantMismatch target method field
      | (.inr (.inl (.inr (.inl (.inr slot))))) => .notControllable slot
      | (.inr (.inl (.inr (.inr (.inl (slot, sender)))))) => .notSender slot sender
      | (.inr (.inl (.inr (.inr (.inr (slot, reason)))))) => .slotInbox slot reason
      | (.inr (.inr (.inl (.inl (.inl (target, method, reason)))))) => .lawDenied target method reason
      | (.inr (.inr (.inl (.inl (.inr ()))))) => .exhausted
      | (.inr (.inr (.inl (.inr (.inl (sender, target)))))) => .queueFull sender target
      | (.inr (.inr (.inl (.inr (.inr slot))))) => .slotQueueFull slot
      | (.inr (.inr (.inr (.inl (.inl slot))))) => .notPipelinable slot
      | (.inr (.inr (.inr (.inl (.inr slot))))) => .slotTaken slot
      | (.inr (.inr (.inr (.inr (.inl (sender, target)))))) => .inboxCodec sender target
      | (.inr (.inr (.inr (.inr (.inr (.inl cell)))))) => .packageCell cell
      | (.inr (.inr (.inr (.inr (.inr (.inr target)))))) => .drainConflict target
    )
    (by intro value; cases value <;> rfl)

/-- Extraction-account layers are a length-prefixed byte list of pairs. -/
def callRefusalStream : StreamCodec ObjectiveCall.CallRefusal :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.list (StreamCodec.product StreamCodec.nat StreamCodec.nat))
      callRefusalTerminalStream)
    splitCallRefusal joinCallRefusal join_split_callRefusal

/-- Every call refusal, including any number of extraction-account layers,
roundtrips as a prefix while preserving arbitrary following bytes. -/
theorem callRefusalStream_prefix_roundtrip (reason : ObjectiveCall.CallRefusal)
    (suffix : List UInt8) :
    callRefusalStream.decodePrefix (callRefusalStream.encode reason ++ suffix) = some (reason, suffix) :=
  callRefusalStream.decodePrefix_encode reason suffix

/-- The refusal roundtrip now states the live byte representation rather than
an unused generic natural-number code. -/
@[simp] theorem callRefusal_encode_roundtrip (reason : ObjectiveCall.CallRefusal) :
    callRefusalStream.toLawful.decode (callRefusalStream.encode reason) = some reason :=
  callRefusalStream.toLawful.decode_encode reason

theorem callRefusalStream_injective : Function.Injective callRefusalStream.encode := by
  intro first second same
  have decoded := congrArg callRefusalStream.toLawful.decode same
  rw [callRefusal_encode_roundtrip, callRefusal_encode_roundtrip] at decoded
  exact Option.some.inj decoded

private def frontEndStream : StreamCodec ObjectiveCall.FrontEnd :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
    (fun value => (value.source, value.core, value.postageSource, value.postageCore))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro value; cases value; rfl)

private def messageRefusalStream : StreamCodec (ObjectiveSend.MessageRefusal) :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.sum (StreamCodec.product StreamCodec.nat StreamCodec.nat)
      (StreamCodec.product StreamCodec.nat StreamCodec.nat))
      (StreamCodec.sum digestStream
      (StreamCodec.sum stringStream
      activityRefusalStream)))
    (fun value => match value with
      | .noInbox sender target => (.inl (.inl (sender, target)))
      | .empty sender target => (.inl (.inr (sender, target)))
      | .staleHead head => (.inr (.inl head))
      | .replySlot reason => (.inr (.inr (.inl reason)))
      | .kernel reason => (.inr (.inr (.inr reason)))
    )
    (fun wire => match wire with
      | (.inl (.inl (sender, target))) => .noInbox sender target
      | (.inl (.inr (sender, target))) => .empty sender target
      | (.inr (.inl head)) => .staleHead head
      | (.inr (.inr (.inl reason))) => .replySlot reason
      | (.inr (.inr (.inr reason))) => .kernel reason
    )
    (by intro value; cases value <;> rfl)

private def signatureErrorStream : StreamCodec (CredentialSignatureIO.Error) :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.sum unitStream
      unitStream)
      (StreamCodec.sum (StreamCodec.product uint32Stream stringStream)
      (StreamCodec.sum unitStream
      stringStream)))
    (fun value => match value with
      | .publicKeyLength => (.inl (.inl ()))
      | .signatureLength => (.inl (.inr ()))
      | .processFailed exitCode detail => (.inr (.inl (exitCode, detail)))
      | .malformedResponse => (.inr (.inr (.inl ())))
      | .unavailable detail => (.inr (.inr (.inr detail)))
    )
    (fun wire => match wire with
      | (.inl (.inl ())) => .publicKeyLength
      | (.inl (.inr ())) => .signatureLength
      | (.inr (.inl (exitCode, detail))) => .processFailed exitCode detail
      | (.inr (.inr (.inl ()))) => .malformedResponse
      | (.inr (.inr (.inr detail))) => .unavailable detail
    )
    (by intro value; cases value <;> rfl)

private def signatureFailureStream : StreamCodec (CredentialSignedEnvelopeController.Failure CredentialSignatureIO.Error) :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum unitStream
      unitStream)
      (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      unitStream)))
      (StreamCodec.sum (StreamCodec.sum unitStream
      unitStream)
      (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      unitStream))))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum unitStream
      unitStream)
      (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      unitStream)))
      (StreamCodec.sum (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      unitStream))
      (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      signatureErrorStream)))))
    (fun value => match value with
      | .malformedState => (.inl (.inl (.inl (.inl ()))))
      | .malformedRegistry => (.inl (.inl (.inl (.inr ()))))
      | .malformedEnvelope => (.inl (.inl (.inr (.inl ()))))
      | .wrongStateVersion => (.inl (.inl (.inr (.inr (.inl ())))))
      | .wrongRegistryVersion => (.inl (.inl (.inr (.inr (.inr ())))))
      | .wrongEnvelopeVersion => (.inl (.inr (.inl (.inl ()))))
      | .staleAuthority => (.inl (.inr (.inl (.inr ()))))
      | .uncommittedRegistry => (.inl (.inr (.inr (.inl ()))))
      | .staleRegistry => (.inl (.inr (.inr (.inr (.inl ())))))
      | .footprintStale => (.inl (.inr (.inr (.inr (.inr ())))))
      | .expired => (.inr (.inl (.inl (.inl ()))))
      | .wrongDomain => (.inr (.inl (.inl (.inr ()))))
      | .wrongMessage => (.inr (.inl (.inr (.inl ()))))
      | .replayedNullifier => (.inr (.inl (.inr (.inr (.inl ())))))
      | .unknownKey => (.inr (.inl (.inr (.inr (.inr ())))))
      | .wrongSubject => (.inr (.inr (.inl (.inl ()))))
      | .wrongKeyEpoch => (.inr (.inr (.inl (.inr (.inl ())))))
      | .wrongAlgorithm => (.inr (.inr (.inl (.inr (.inr ())))))
      | .staleKey => (.inr (.inr (.inr (.inl ()))))
      | .invalidSignature => (.inr (.inr (.inr (.inr (.inl ())))))
      | .nativeVerify error => (.inr (.inr (.inr (.inr (.inr error)))))
    )
    (fun wire => match wire with
      | (.inl (.inl (.inl (.inl ())))) => .malformedState
      | (.inl (.inl (.inl (.inr ())))) => .malformedRegistry
      | (.inl (.inl (.inr (.inl ())))) => .malformedEnvelope
      | (.inl (.inl (.inr (.inr (.inl ()))))) => .wrongStateVersion
      | (.inl (.inl (.inr (.inr (.inr ()))))) => .wrongRegistryVersion
      | (.inl (.inr (.inl (.inl ())))) => .wrongEnvelopeVersion
      | (.inl (.inr (.inl (.inr ())))) => .staleAuthority
      | (.inl (.inr (.inr (.inl ())))) => .uncommittedRegistry
      | (.inl (.inr (.inr (.inr (.inl ()))))) => .staleRegistry
      | (.inl (.inr (.inr (.inr (.inr ()))))) => .footprintStale
      | (.inr (.inl (.inl (.inl ())))) => .expired
      | (.inr (.inl (.inl (.inr ())))) => .wrongDomain
      | (.inr (.inl (.inr (.inl ())))) => .wrongMessage
      | (.inr (.inl (.inr (.inr (.inl ()))))) => .replayedNullifier
      | (.inr (.inl (.inr (.inr (.inr ()))))) => .unknownKey
      | (.inr (.inr (.inl (.inl ())))) => .wrongSubject
      | (.inr (.inr (.inl (.inr (.inl ()))))) => .wrongKeyEpoch
      | (.inr (.inr (.inl (.inr (.inr ()))))) => .wrongAlgorithm
      | (.inr (.inr (.inr (.inl ())))) => .staleKey
      | (.inr (.inr (.inr (.inr (.inl ()))))) => .invalidSignature
      | (.inr (.inr (.inr (.inr (.inr error))))) => .nativeVerify error
    )
    (by intro value; cases value <;> rfl)

private def signatureRejectStream : StreamCodec (CredentialSignatureAdmission.Reject) :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      unitStream))
      (StreamCodec.sum unitStream
      (StreamCodec.sum unitStream
      unitStream)))
      (StreamCodec.sum (StreamCodec.sum unitStream
      (StreamCodec.sum signatureFailureStream
      unitStream))
      (StreamCodec.sum (StreamCodec.sum unitStream
      (StreamCodec.list StreamCodec.byte))
      (StreamCodec.sum (StreamCodec.product StreamCodec.nat StreamCodec.nat)
      unitStream))))
    (fun value => match value with
      | .wrongDomain => (.inl (.inl (.inl ())))
      | .missingCurrentKey => (.inl (.inl (.inr (.inl ()))))
      | .subjectKeyEpoch => (.inl (.inl (.inr (.inr ()))))
      | .unregisteredKey => (.inl (.inr (.inl ())))
      | .revokedKey => (.inl (.inr (.inr (.inl ()))))
      | .unsupportedAlgorithm => (.inl (.inr (.inr (.inr ()))))
      | .publicKeyLength => (.inr (.inl (.inl ())))
      | .envelope reason => (.inr (.inl (.inr (.inl reason))))
      | .sourceBinding => (.inr (.inl (.inr (.inr ()))))
      | .malformedFootprint => (.inr (.inr (.inl (.inl ()))))
      | .footprintStale address => (.inr (.inr (.inl (.inr address))))
      | .expired height validUntil => (.inr (.inr (.inr (.inl (height, validUntil)))))
      | .unvouched => (.inr (.inr (.inr (.inr ()))))
    )
    (fun wire => match wire with
      | (.inl (.inl (.inl ()))) => .wrongDomain
      | (.inl (.inl (.inr (.inl ())))) => .missingCurrentKey
      | (.inl (.inl (.inr (.inr ())))) => .subjectKeyEpoch
      | (.inl (.inr (.inl ()))) => .unregisteredKey
      | (.inl (.inr (.inr (.inl ())))) => .revokedKey
      | (.inl (.inr (.inr (.inr ())))) => .unsupportedAlgorithm
      | (.inr (.inl (.inl ()))) => .publicKeyLength
      | (.inr (.inl (.inr (.inl reason)))) => .envelope reason
      | (.inr (.inl (.inr (.inr ())))) => .sourceBinding
      | (.inr (.inr (.inl (.inl ())))) => .malformedFootprint
      | (.inr (.inr (.inl (.inr address)))) => .footprintStale address
      | (.inr (.inr (.inr (.inl (height, validUntil))))) => .expired height validUntil
      | (.inr (.inr (.inr (.inr ())))) => .unvouched
    )
    (by intro value; cases value <;> rfl)

/-- Typed byte representation: constructor tags, concatenated fields and
length-prefixed lists. No payload or recursive layer is a paired Nat code. -/
def rejectStream : StreamCodec (Reject) :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum unitStream
      unitStream)
      (StreamCodec.sum unitStream
      unitStream))
      (StreamCodec.sum (StreamCodec.sum unitStream
      unitStream)
      (StreamCodec.sum unitStream
      activityRefusalStream)))
      (StreamCodec.sum (StreamCodec.sum (StreamCodec.sum seatStoreRefusalStream
      (StreamCodec.product callRefusalStream frontEndStream))
      (StreamCodec.sum messageRefusalStream
      unitStream))
      (StreamCodec.sum (StreamCodec.sum unitStream
      unitStream)
      (StreamCodec.sum (StreamCodec.product digestStream digestStream)
      signatureRejectStream))))
    (fun value => match value with
      | .malformedIngress => (.inl (.inl (.inl (.inl ()))))
      | .directoryUnavailable => (.inl (.inl (.inl (.inr ()))))
      | .authorityUnavailable => (.inl (.inl (.inr (.inl ()))))
      | .staleAuthority => (.inl (.inl (.inr (.inr ()))))
      | .replayedMarker => (.inl (.inr (.inl (.inl ()))))
      | .physicalPreparation => (.inl (.inr (.inl (.inr ()))))
      | .inputUndecodable => (.inl (.inr (.inr (.inl ()))))
      | .kernel reason => (.inl (.inr (.inr (.inr reason))))
      | .seats reason => (.inr (.inl (.inl (.inl reason))))
      | .call reason drawn => (.inr (.inl (.inl (.inr (reason, drawn)))))
      | .message reason => (.inr (.inl (.inr (.inl reason))))
      | .staleAwait => (.inr (.inl (.inr (.inr ()))))
      | .notObjectHolder => (.inr (.inr (.inl (.inl ()))))
      | .notAccountOwner => (.inr (.inr (.inl (.inr ()))))
      | .outcomeMoved claimed decided => (.inr (.inr (.inr (.inl (claimed, decided)))))
      | .signature reason => (.inr (.inr (.inr (.inr reason))))
    )
    (fun wire => match wire with
      | (.inl (.inl (.inl (.inl ())))) => .malformedIngress
      | (.inl (.inl (.inl (.inr ())))) => .directoryUnavailable
      | (.inl (.inl (.inr (.inl ())))) => .authorityUnavailable
      | (.inl (.inl (.inr (.inr ())))) => .staleAuthority
      | (.inl (.inr (.inl (.inl ())))) => .replayedMarker
      | (.inl (.inr (.inl (.inr ())))) => .physicalPreparation
      | (.inl (.inr (.inr (.inl ())))) => .inputUndecodable
      | (.inl (.inr (.inr (.inr reason)))) => .kernel reason
      | (.inr (.inl (.inl (.inl reason)))) => .seats reason
      | (.inr (.inl (.inl (.inr (reason, drawn))))) => .call reason drawn
      | (.inr (.inl (.inr (.inl reason)))) => .message reason
      | (.inr (.inl (.inr (.inr ())))) => .staleAwait
      | (.inr (.inr (.inl (.inl ())))) => .notObjectHolder
      | (.inr (.inr (.inl (.inr ())))) => .notAccountOwner
      | (.inr (.inr (.inr (.inl (claimed, decided))))) => .outcomeMoved claimed decided
      | (.inr (.inr (.inr (.inr reason)))) => .signature reason
    )
    (by intro value; cases value <;> rfl)

def rejectCodec : LawfulCodec Reject :=
  ObjectiveActivityWire.framed "DREGG/OBJECTIVE/ACTIVITY/REJECT/v2".toUTF8.toList rejectStream

@[simp] theorem rejectCodec_roundtrip (cause : Reject) :
    rejectCodec.decode (rejectCodec.encode cause) = some cause :=
  rejectCodec.decode_encode cause

/-- Universal prefix roundtrip, including arbitrary following bytes. -/
theorem rejectStream_prefix_roundtrip (cause : Reject) (suffix : List UInt8) :
    rejectStream.decodePrefix (rejectStream.encode cause ++ suffix) = some (cause, suffix) :=
  rejectStream.decodePrefix_encode cause suffix

/-- Equal refusal bytes imply the same typed cause; no rendering is discarded. -/
theorem rejectCodec_injective : Function.Injective rejectCodec.encode := by
  intro first second same
  have decoded := congrArg rejectCodec.decode same
  rw [rejectCodec.decode_encode, rejectCodec.decode_encode] at decoded
  exact Option.some.inj decoded

/-- The former paired-natural payload is a different codec edition and
refuses even if its body happens to be valid under the new byte stream. -/
theorem rejectCodec_v1_refuses (body : List UInt8) :
    rejectCodec.decode ("DREGG/OBJECTIVE/ACTIVITY/REJECT/v1".toUTF8.toList ++ body) = none := by
  cases found : rejectCodec.decode ("DREGG/OBJECTIVE/ACTIVITY/REJECT/v1".toUTF8.toList ++ body) with
  | none => rfl
  | some value =>
    have canon := ObjectiveActivityWire.framed_canonical found
    have cut := congrArg (List.take "DREGG/OBJECTIVE/ACTIVITY/REJECT/v1".toUTF8.toList.length) canon
    change ("DREGG/OBJECTIVE/ACTIVITY/REJECT/v2".toUTF8.toList ++
      _).take _ = ("DREGG/OBJECTIVE/ACTIVITY/REJECT/v1".toUTF8.toList ++ body).take _ at cut
    rw [List.take_append_of_le_length (by decide +kernel), List.take_left' rfl] at cut
    exact absurd cut (by decide +kernel)

/-- The payload installed in a charged failure's durable `StableEvent`.  The
source event remains the original ingress event and therefore retains the
original receipt/event id. -/
structure RecordedFailure where
  source : StableEvent
  cause : Reject

def recordedEventStream : StreamCodec StableEvent :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)))
    (fun value => (value.codecVersion, value.domain, value.eventId, value.canonicalBytes))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro value; cases value; rfl)

def recordedFailureStream : StreamCodec RecordedFailure :=
  StreamCodec.xmap (StreamCodec.product recordedEventStream rejectStream)
    (fun value => (value.source, value.cause))
    (fun value => ⟨value.1, value.2⟩)
    (by intro value; cases value; rfl)

def recordedFailureCodec : LawfulCodec RecordedFailure :=
  ObjectiveActivityWire.framed
    "DREGG/OBJECTIVE/ACTIVITY/RECORDED-FAILURE/v2".toUTF8.toList recordedFailureStream

/-- The former paired-natural payload is a different codec edition and
refuses even if its body happens to be valid under the new byte stream. -/
theorem recordedFailureCodec_v1_refuses (body : List UInt8) :
    recordedFailureCodec.decode ("DREGG/OBJECTIVE/ACTIVITY/RECORDED-FAILURE/v1".toUTF8.toList ++ body) = none := by
  cases found : recordedFailureCodec.decode ("DREGG/OBJECTIVE/ACTIVITY/RECORDED-FAILURE/v1".toUTF8.toList ++ body) with
  | none => rfl
  | some value =>
    have canon := ObjectiveActivityWire.framed_canonical found
    have cut := congrArg (List.take "DREGG/OBJECTIVE/ACTIVITY/RECORDED-FAILURE/v1".toUTF8.toList.length) canon
    change ("DREGG/OBJECTIVE/ACTIVITY/RECORDED-FAILURE/v2".toUTF8.toList ++
      _).take _ = ("DREGG/OBJECTIVE/ACTIVITY/RECORDED-FAILURE/v1".toUTF8.toList ++ body).take _ at cut
    rw [List.take_append_of_le_length (by decide +kernel), List.take_left' rfl] at cut
    exact absurd cut (by decide +kernel)

/-- A charged record is a version-2 activity event whose canonical payload is
the original version-1 ingress event plus the exact typed refusal. -/
def failedEvent (source : StableEvent) (cause : Reject) : StableEvent :=
  { source with codecVersion := 2
                canonicalBytes := recordedFailureCodec.encode ⟨source, cause⟩ }

/-- The real terminal disposition decoded from a durable record. -/
inductive RecordedDisposition where
  | confirmed
  | charged (cause : Reject)

/-- Decode the objective-activity record shape.  Version 1 is a successful
record. Version 2 must decode canonically and repeat the outer domain/event id;
unknown or inconsistent shapes fail closed. -/
def recordedDisposition (stored : StableEvent) : Option (StableEvent × RecordedDisposition) :=
  if stored.codecVersion = 1 then some (stored, .confirmed)
  else if stored.codecVersion = 2 then do
    let failure ← recordedFailureCodec.decode stored.canonicalBytes
    if failure.source.codecVersion = 1 ∧ failure.source.domain = stored.domain ∧
        failure.source.eventId = stored.eventId then
      some (failure.source, .charged failure.cause)
    else none
  else none

@[simp] theorem recordedDisposition_event (domain semantics : Digest) (ingress : DecodedIngress) :
    recordedDisposition (event domain semantics ingress) =
      some (event domain semantics ingress, .confirmed) := by
  simp [recordedDisposition, event]

@[simp] theorem recordedDisposition_failedEvent (domain semantics : Digest) (ingress : DecodedIngress)
    (cause : Reject) :
    recordedDisposition (failedEvent (event domain semantics ingress) cause) =
      some (event domain semantics ingress, .charged cause) := by
  unfold recordedDisposition failedEvent
  simp only [event]
  rw [if_neg (by decide), if_pos (by decide), recordedFailureCodec.decode_encode]
  simp

/-- The charge of a paying turn's failure: the turn's payer account, its declared envelope, and the
transaction the turn would have committed under (so a retry of the same ingress replays it). -/
def failureRequest (domain semantics : Digest) (command : Command) : Option ObjectiveActivity.FailureRequest :=
  match command.turn with
  | .birth _ _ account _ _ _ envelope _ _ _ =>
      some ⟨account, envelope, (transactionOf command).getD ⟨marker domain semantics command⟩⟩
  | .invoke _ _ _ _ _ envelope _ _ account _ =>
      some ⟨account, envelope, (transactionOf command).getD ⟨marker domain semantics command⟩⟩
  | _ => none

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

/-- The physical shape every committed activity intent has. -/
def IntentShape (deployment : Deployment) (durable : Durable) (intent : DataIntent rootBytes) : Prop :=
  (intent.writes.map DataWrite.cellId).Nodup ∧
    (∀ write ∈ intent.writes, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ intent.writes, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ write ∈ intent.writes, ActivityOrBook deployment write) ∧
    (∀ guard ∈ intent.readGuards, guard.expectedRoot = durable.snapshot.model.roots guard.cellId) ∧
    (∀ write ∈ intent.writes, ObjectiveActivity.isRetired (durable.snapshot.canonicalBytes write.cellId) = false)

instance intentShapeDecidable (deployment : Deployment) (durable : Durable) (intent : DataIntent rootBytes) :
    Decidable (IntentShape deployment durable intent) := by
  unfold IntentShape
  infer_instance

def PhysicalShape (prepared : Prepared deployment profile ambient durable command) (ingress : DecodedIngress) :
    Prop :=
  let intent := prepared.intent ingress
  (intent.writes.map DataWrite.cellId).Nodup ∧
    (∀ write ∈ intent.writes, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ intent.writes, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ write ∈ intent.writes, ActivityOrBook deployment write) ∧
    (∀ guard ∈ intent.readGuards, guard.expectedRoot = durable.snapshot.model.roots guard.cellId) ∧
    (∀ write ∈ intent.writes, ObjectiveActivity.isRetired (durable.snapshot.canonicalBytes write.cellId) = false)

instance physicalShapeDecidable (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) : Decidable (PhysicalShape prepared ingress) := by
  unfold PhysicalShape
  infer_instance

/-- An accepted turn: gated, its signature verified over the claimed outcome, decided to exactly
that outcome. -/
structure Accepted [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  gated : Gated deployment profile ambient durable ingress.command ingress.ingress.outcome
  receipt : CredentialSignatureAdmission.CheckedSignature gated.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.envelope
  prepared : Prepared deployment profile ambient durable ingress.command
  preparedExact : prepare gated = .ok prepared
  physical : PhysicalShape prepared ingress

/-- The intent of a charged failure: the kernel's `failed` turn (the Book only) under this
receiver's seal. -/
def failedIntent (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (config : Config) (ingress : DecodedIngress) (cause : Reject)
    (request : ObjectiveActivity.FailureRequest)
    (failure : ObjectiveActivity.ChargedFailure config durable.snapshot request)
    (final : List Post × List ReadGuard) : DataIntent rootBytes :=
  ActivitySeatEnd.AdmittedTurn.finalIntent
    { sealAt (profile := profile) authority ingress.command ingress with
      event := failedEvent (event deployment.domain profile.semantics ingress) cause }
    final.1 final.2 (ObjectiveActivity.AdmittedTurn.failed (height := ambient.height) request failure)

/-- **A CHARGED FAILURE** (GPT-6 row E): gated (authority, capabilities, funds), its signature
verified, and its decision refused for a charged cause (`chargedCause`: after the validator's
work, or an outcome other than the signed one). It commits the kernel's `failed` turn: the
public price of the declared envelope, payer to collector, and nothing else; the marker is spent. -/
structure Failed [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  gated : Gated deployment profile ambient durable ingress.command ingress.ingress.outcome
  receipt : CredentialSignatureAdmission.CheckedSignature gated.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.envelope
  cause : Reject
  causeExact : prepare gated = .error cause
  charged : chargedCause cause = true
  request : ObjectiveActivity.FailureRequest
  requestExact : failureRequest deployment.domain profile.semantics ingress.command = some request
  failure : ObjectiveActivity.ChargedFailure gated.config durable.snapshot request
  final : List Post × List ReadGuard
  finalExact : ActivitySeatEnd.finish gated.config durable.snapshot ambient.height
    (ObjectiveActivity.AdmittedTurn.failed request failure) = .ok final
  physical : IntentShape deployment durable
    (failedIntent (profile := profile) (ambient := ambient) gated.authority gated.config ingress cause
      request failure final)

/-- What admission decides for a signed ingress: an accepted turn, or a charged failure. -/
inductive Verdict [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  | accepted (accepted : Accepted deployment profile ambient durable ingress)
  | failed (failed : Failed deployment profile ambient durable ingress)

/-- Admission: the gate, the signature, then the decision. A refusal before the decision (the
gate, the signature) commits nothing and charges nothing. A decision refused for a charged
cause commits a charged failure; any other refusal commits nothing. -/
def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (Verdict deployment profile ambient durable ingress)) := do
  match gate deployment profile ambient durable ingress.command ingress.ingress.outcome with
  | .error reason => return .error reason
  | .ok gated =>
    let ⟨_, request⟩ := gated.request
    match ← CredentialSignatureAdmission.verifyNative native gated.authority.snapshot
        (marker gated.authority.snapshot.domain profile.semantics ingress.command)
        request ingress.ingress.envelope with
    | .error reason => return .error (.signature reason)
    | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.ingress.envelope then
        match preparedExact : prepare gated with
        | .ok prepared =>
          if physical : PhysicalShape prepared ingress then
            return .ok (.accepted ⟨gated, receipt, same, prepared, preparedExact, physical⟩)
          else return .error .physicalPreparation
        | .error cause =>
          if charged : chargedCause cause = true then
            match requestExact : failureRequest deployment.domain profile.semantics ingress.command with
            | none => return .error cause
            | some failing =>
              match ObjectiveActivity.chargeFailure gated.config durable.snapshot failing with
              | .error _ => return .error cause
              | .ok failure =>
                match finalExact : ActivitySeatEnd.finish gated.config durable.snapshot ambient.height
                    (ObjectiveActivity.AdmittedTurn.failed failing failure) with
                | .error _ => return .error cause
                | .ok final =>
                  if physical : IntentShape deployment durable
                      (failedIntent (profile := profile) (ambient := ambient) gated.authority gated.config ingress
                        cause failing failure final) then
                    return .ok (.failed ⟨gated, receipt, same, cause, preparedExact, charged, failing, requestExact,
                      failure, final, finalExact, physical⟩)
                  else return .error .physicalPreparation
          else return .error cause
      else return .error (.signature (.envelope .invalidSignature))

/-- **A refusal at the gate decides, verifies and commits nothing.** -/
theorem gate_refusal_runs_nothing [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    {ingress : DecodedIngress} {reason : Reject}
    (refused : gate deployment profile ambient durable ingress.command ingress.ingress.outcome = .error reason) :
    admitDecodedNative deployment profile ambient durable native ingress = pure (.error reason) := by
  unfold admitDecodedNative
  rw [refused]

variable [DecidableEq F] {ingress : DecodedIngress}

def intent (accepted : Accepted deployment profile ambient durable ingress) : DataIntent rootBytes :=
  accepted.prepared.intent ingress

def Failed.intent (failed : Failed deployment profile ambient durable ingress) : DataIntent rootBytes :=
  failedIntent (profile := profile) (ambient := ambient) failed.gated.authority failed.gated.config ingress
    failed.cause failed.request failed.failure failed.final

def Verdict.intent : Verdict deployment profile ambient durable ingress → DataIntent rootBytes
  | .accepted admitted => Minidregg.Kernel.ObjectiveActivityReceiver.intent admitted
  | .failed charged => charged.intent

/-- Every admitted operation, including a charged failure, leaves permanently
retired identifiers untouched. This is checked at native admission against the
same loaded snapshot whose roots are checked by PhysicalShape/IntentShape. -/
theorem Verdict.writes_unretired (verdict : Verdict deployment profile ambient durable ingress)
    (write : DataWrite) (member : write ∈ verdict.intent.writes) :
    ObjectiveActivity.isRetired (durable.snapshot.canonicalBytes write.cellId) = false := by
  cases verdict with
  | accepted accepted => exact accepted.physical.2.2.2.2.2 write member
  | failed failed => exact failed.physical.2.2.2.2.2 write member

#assert_axioms Verdict.writes_unretired

/-- **A charged failure charges and rolls back.** Every write of a charged failure's intent is the
Book cell, there is exactly one, and the batch it posts is exactly the fee of the declared
envelope's public price from the payer to the collector: no record, state, slot, purse, seat or
object cell is written. -/
theorem failed_charges_and_rolls_back (failed : Failed deployment profile ambient durable ingress) :
    failed.intent.writes.length = 1 ∧
    (∀ write ∈ failed.intent.writes, write.cellId = failed.gated.config.bookCell) ∧
    failed.failure.posted.batch =
      ⟨[], [.fee failed.request.account failed.gated.config.collector failed.gated.config.asset
        (failed.gated.config.tariff.workOf failed.request.envelope)], []⟩ := by
  obtain ⟨seats, domains, units, finalized, _, _, _⟩ := ActivitySeatEnd.finish_finalize failed.finalExact
  unfold ActivitySeatEnd.finalize at finalized
  simp only [ActivitySeatEnd.AdmittedTurn.ending] at finalized
  have posts : failed.final.1 = failed.failure.posts := by
    have := congrArg Prod.fst (Except.ok.inj finalized)
    simpa [ObjectiveActivity.AdmittedTurn.posts] using this.symm
  have writes : failed.intent.writes = failed.failure.posts.map (Post.write rootBytes) := by
    simp [Failed.intent, failedIntent, ActivitySeatEnd.AdmittedTurn.finalIntent, intentOf, posts]
  obtain ⟨cells, batch⟩ := ObjectiveActivity.ChargedFailure.charges_only_the_book failed.failure
  refine ⟨by simp [writes, ObjectiveActivity.ChargedFailure.posts], fun write member => ?_, batch⟩
  rw [writes] at member
  obtain ⟨post, inPosts, rfl⟩ := List.mem_map.mp member
  exact cells post inPosts

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
  have finished : ActivitySeatEnd.finish accepted.prepared.config durable.snapshot ambient.height
      accepted.prepared.decided = .ok (accepted.prepared.final.1, accepted.prepared.final.2) :=
    accepted.prepared.finalExact
  obtain ⟨seats, _, _, final, _, _, _⟩ := ActivitySeatEnd.finish_finalize finished
  unfold ActivitySeatEnd.finalize at final
  rw [ends] at final
  simp only at final
  split at final
  · cases final
  · rename_i none_
    exact absurd (ActivitySeatEnd.join_none none_) holds
  · rename_i joined _
    have same := congrArg Prod.fst (Except.ok.inj final).symm
    exact ⟨joined, same, joined.closes.1, joined.closes.2.1⟩

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

/-- An invocation's operation id is its command `nonce` (the Host's invoke JSON
names it `opId`). It is signed, claimed through `marker` in the spent map, and
hashed into `ObjectiveCall.invokeTransaction`, hence into every message id the
invocation sends (`Inbox.sendId`). A retry of the operation reuses it. -/
def Command.isInvoke (command : Command) : Bool :=
  match command.turn with
  | .invoke .. => true
  | _ => false

/-- What a recorded transaction answers an ingress under its id: the RECORDED
receipt and terminal disposition, for the exact ingress (`exact`) or for an
invocation re-signed under the same operation id (`retry`). -/
inductive Replayed where
  | exact (receipt : Receipt) (disposition : RecordedDisposition)
  | retry (receipt : Receipt) (disposition : RecordedDisposition)

/-- A retained ingress finds its record by its transaction id. The exact
ingress replays (`exact`). An invocation re-signed under the same operation id
is a `retry`. That covers a retry after a lost answer, which is re-planned, so
its bytes differ. Its transaction id binds the subject, the call and the op id,
so it names the same operation. It is answered with the original's receipt
only once its signature verifies under the subject's key (`verifyRetry`), and
it commits nothing. A changed postage or allowance does not matter, since the
id leaves both out. Any other ingress under the same id (another delivery of
the same await, another decision of the same slot) is a conflict. -/
def replay (domain semantics : Digest) (durable : Durable) (ingress : DecodedIngress) :
    Option (Except Unit Replayed) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded
      (transactionId domain semantics ingress) durable.snapshot.model.journal with
  | none => none
  | some recorded =>
    if recorded.transactionId = transactionId domain semantics ingress then
      match recordedDisposition recorded.event.event with
      | some (source, disposition) =>
        if source = event domain semantics ingress then
          some (.ok (.exact ⟨recorded.transactionId, source.eventId⟩ disposition))
        else if ingress.command.isInvoke then
          some (.ok (.retry ⟨recorded.transactionId, source.eventId⟩ disposition))
        else some (.error ())
      | none => some (.error ())
    else some (.error ())

/-- **A recorded invocation, re-signed, is a retry of the recorded operation**,
carrying the recorded receipt (the original transaction and event). -/
theorem replay_invoke_recorded {domain semantics : Digest} {durable : Durable} {ingress : DecodedIngress}
    {recorded source disposition} (found : DurableCommitProtocol.Snapshot.lookupRecorded
      (transactionId domain semantics ingress) durable.snapshot.model.journal = some recorded)
    (same : recorded.transactionId = transactionId domain semantics ingress)
    (terminal : recordedDisposition recorded.event.event = some (source, disposition))
    (resigned : source ≠ event domain semantics ingress)
    (invoke : ingress.command.isInvoke = true) :
    replay domain semantics durable ingress =
      some (.ok (.retry ⟨recorded.transactionId, source.eventId⟩ disposition)) := by
  simp [replay, found, same, terminal, resigned, invoke]

/-- The exact ingress still answers exactly its own receipt. -/
theorem replay_exact {domain semantics : Digest} {durable : Durable} {ingress : DecodedIngress}
    {recorded disposition} (found : DurableCommitProtocol.Snapshot.lookupRecorded
      (transactionId domain semantics ingress) durable.snapshot.model.journal = some recorded)
    (same : recorded.transactionId = transactionId domain semantics ingress)
    (terminal : recordedDisposition recorded.event.event =
      some (event domain semantics ingress, disposition)) :
    replay domain semantics durable ingress =
      some (.ok (.exact (receipt domain semantics ingress) disposition)) := by
  simp [replay, found, same, terminal, receipt]

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  /-- A CHARGED FAILURE committed: the price of the declared envelope was posted, nothing else
  was written, the marker is spent; `cause` is why the decision failed. -/
  | charged (kind : DurableReceiverIO.Confirmation) (receipt : Receipt) (cause : Reject)
  | rejected (reason : Reject)
  | transactionConflict
  | durableRejected (reason : DurableDataIntent.RejectReason)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

/-- The outcome a plan shows its signer: the decided turn's posts, or no posts
when the kernel refuses the command. `signingHeader` signs over it, and
`verifyRetry` checks a retry's signature over the same value. -/
def planOutcome (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) : Digest :=
  match configOf deployment profile ambient with
  | .ok config => match decideTurn config durable.snapshot ambient.height command with
    | .ok decided => match ActivitySeatEnd.finish config durable.snapshot ambient.height decided with
      | .ok final => outcomeDigest final.1
      | .error _ => outcomeDigest []
    | .error _ => outcomeDigest []
  | .error _ => outcomeDigest []

/-- The authority a retry's signature is checked against is the snapshot
admission uses, with one exception: the retried operation's own marker is not
counted as consumed, because that operation consumed it. Every other marker,
the keys, the root and the revision are unchanged. -/
def retrySnapshot (snapshot : CredentialAuthorityDomain.Snapshot) (claimed : Nat) :
    CredentialAuthorityDomain.Snapshot :=
  { snapshot with spent := fun n => n != claimed && snapshot.spent n }

/-- **A retry is answered only under the operation's own authority**: its
signature must verify, by the command subject's current key, over the header
its plan showed (the outcome its ingress carries). This is the same `verifyNative` admission runs.
Without the check, anyone holding the content could use the replay answer as
an existence oracle for another subject's operation. Nothing commits either
way. -/
def verifyRetry (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig) (durable : Durable)
    (ingress : DecodedIngress) : IO (Except Reject Unit) := do
  let some authority := loadDeployment deployment durable.snapshot
    | return .error .authorityUnavailable
  let command := ingress.command
  let claimed := marker authority.snapshot.domain profile.semantics command
  let preRoot := durable.snapshot.model.roots ⟨(signedTarget deployment.domain command).2⟩
  -- the outcome the signer signed travels with the ingress (row E): the retry is checked over exactly it
  let ⟨_, request⟩ := signedRequest authority.snapshot profile.semantics ambient command preRoot
    ingress.ingress.outcome
  match ← CredentialSignatureAdmission.verifyNative native (retrySnapshot authority.snapshot claimed) claimed
      request ingress.ingress.envelope with
  | .error reason => return .error (.signature reason)
  | .ok _ => return .ok ()

/-- Turn a durable record's terminal disposition into its replay answer. -/
def dispositionAnswer (prior : Receipt) : RecordedDisposition → Result
  | .confirmed => .confirmed .replayed prior
  | .charged cause => .charged .replayed prior cause

/-- How a verified-or-refused retry is answered: the recorded receipt and
terminal disposition, or the named refusal. A refused retry is never answered
with either recorded disposition. -/
def retryAnswer (verified : Except Reject Unit) (prior : Receipt)
    (disposition : RecordedDisposition) : Result :=
  match verified with
  | .ok () => dispositionAnswer prior disposition
  | .error reason => .rejected reason

/-- Pure routing shared by `receiveLoaded`'s exact and verified-retry branches. -/
def replayAnswer (verified : Except Reject Unit) : Replayed → Result
  | .exact prior disposition => dispositionAnswer prior disposition
  | .retry prior disposition => retryAnswer verified prior disposition

/-- The proposition that an answer has the terminal disposition supplied by a
durable record. Its charged case names the record's typed cause directly; it is
deliberately independent of `replayAnswer` and `dispositionAnswer`. -/
def AnswersRecorded (prior : Receipt) (disposition : RecordedDisposition) (answer : Result) : Prop :=
  match disposition with
  | .confirmed => answer = .confirmed .replayed prior
  | .charged cause => answer = .charged .replayed prior cause

/-- **Replay preserves the recorded terminal disposition**, for both an exact
replay and a verified fresh-signature retry.  `disposition` is an input decoded
from the durable record by `replay`; it is not defined from either answer. -/
theorem replayAnswer_preserves_recorded_disposition (prior : Receipt)
    (disposition : RecordedDisposition) :
    AnswersRecorded prior disposition (replayAnswer (.ok ()) (.exact prior disposition)) ∧
      AnswersRecorded prior disposition (replayAnswer (.ok ()) (.retry prior disposition)) := by
  constructor <;> cases disposition <;> rfl

/-- **The receiver's replay routing preserves the disposition decoded from the
actual durable journal entry.**  The same recorded `disposition` reaches the
exact branch and, when the ingress is a verified invocation retry, the retry
branch.  The premise is the record decoder's result, not a definition in terms
of either replay answer. -/
theorem replay_routes_recorded_disposition
    {domain semantics : Digest} {durable : Durable} {ingress : DecodedIngress}
    {recorded source disposition}
    (found : DurableCommitProtocol.Snapshot.lookupRecorded
      (transactionId domain semantics ingress) durable.snapshot.model.journal = some recorded)
    (same : recorded.transactionId = transactionId domain semantics ingress)
    (terminal : recordedDisposition recorded.event.event = some (source, disposition)) :
    (source = event domain semantics ingress →
      replay domain semantics durable ingress =
        some (.ok (.exact ⟨recorded.transactionId, source.eventId⟩ disposition)) ∧
      AnswersRecorded ⟨recorded.transactionId, source.eventId⟩ disposition
        (replayAnswer (.ok ()) (.exact ⟨recorded.transactionId, source.eventId⟩ disposition))) ∧
    (source ≠ event domain semantics ingress → ingress.command.isInvoke = true →
      replay domain semantics durable ingress =
        some (.ok (.retry ⟨recorded.transactionId, source.eventId⟩ disposition)) ∧
      AnswersRecorded ⟨recorded.transactionId, source.eventId⟩ disposition
        (replayAnswer (.ok ()) (.retry ⟨recorded.transactionId, source.eventId⟩ disposition))) := by
  constructor
  · intro exact
    subst source
    constructor
    · simpa [receipt, same] using replay_exact found same terminal
    · exact (replayAnswer_preserves_recorded_disposition _ disposition).1
  · intro changed invoke
    constructor
    · exact replay_invoke_recorded found same terminal changed invoke
    · exact (replayAnswer_preserves_recorded_disposition _ disposition).2

/-- **A retry that does not verify is refused by name, not answered**. -/
theorem retry_unverified_refused (reason : Reject) (prior : Receipt)
    (disposition : RecordedDisposition) :
    retryAnswer (.error reason) prior disposition = .rejected reason ∧
      (∀ kind receipt, retryAnswer (.error reason) prior disposition ≠ .confirmed kind receipt) ∧
      (∀ kind receipt cause,
        retryAnswer (.error reason) prior disposition ≠ .charged kind receipt cause) := by
  constructor
  · rfl
  · constructor
    · intro kind receipt
      simp [retryAnswer]
    · intro kind receipt cause
      simp [retryAnswer]


#assert_axioms sumWithStateRetired_existing
#assert_axioms activityRefusalStream_stateRetired_encode
#assert_axioms activityRefusalStream_stateRetired_prefix

/-- Repeating the same gate has one result; signature proof identity is irrelevant. -/
theorem Gated.unique {claimed : Digest}
    (left right : Gated deployment profile ambient durable command claimed) : left = right := by
  rcases left with ⟨ld, la, lc, lce, lr, lre, lh, lf⟩
  rcases right with ⟨rd, ra, rc, rce, rr, rre, rh, rf⟩
  cases LoadedDirectory.unique ld rd
  cases CredentialAuthorityDomainReceiver.Loaded.unique la ra
  have cfg : lc = rc := Except.ok.inj (lce.symm.trans rce)
  cases cfg
  cases lre
  cases rre
  rfl

/-- Charged failure computation is determined by the Book and request. -/
theorem chargedFailure_unique {ob : Config} {request : ObjectiveActivity.FailureRequest}
    (left right : ObjectiveActivity.ChargedFailure ob durable.snapshot request) : left = right := by
  rcases left with ⟨lb, lbe, lp, lpe⟩
  rcases right with ⟨rb, rbe, rp, rpe⟩
  have book : lb = rb := Except.ok.inj (lbe.symm.trans rbe)
  cases book
  rcases lp with ⟨batch, accepted⟩
  rcases rp with ⟨batch', accepted'⟩
  cases lpe
  cases rpe
  rfl

/-- The same signed ingress on the same opening determines the exact intent,
including charged failures, final Book rewrites and all domain guards. -/
theorem Verdict.intent_determined
    (left right : Verdict deployment profile ambient durable ingress) : left.intent = right.intent := by
  cases left with
  | accepted left =>
    cases right with
    | accepted right =>
      have gated := Gated.unique left.gated right.gated
      have prepared : left.prepared = right.prepared :=
        Except.ok.inj (left.preparedExact.symm.trans (gated ▸ right.preparedExact))
      change left.prepared.intent ingress = right.prepared.intent ingress
      rw [prepared]
    | failed right =>
      have gated := Gated.unique left.gated right.gated
      have bad := left.preparedExact.symm.trans (gated ▸ right.causeExact)
      cases bad
  | failed left =>
    cases right with
    | accepted right =>
      have gated := Gated.unique left.gated right.gated
      have bad := left.causeExact.symm.trans (gated ▸ right.preparedExact)
      cases bad
    | failed right =>
      rcases left with ⟨lg, ls, le, lc, lce, lch, lr, lre, lf, lp, lpe, lph⟩
      rcases right with ⟨rg, rs, re, rc, rce, rch, rr, rre, rf, rp, rpe, rph⟩
      cases Gated.unique lg rg
      have cause : lc = rc := Except.error.inj (lce.symm.trans rce)
      cases cause
      have request : lr = rr := Option.some.inj (lre.symm.trans rre)
      cases request
      cases chargedFailure_unique lf rf
      have posts : lp = rp := Except.ok.inj (lpe.symm.trans rpe)
      cases posts
      rfl

#assert_axioms Gated.unique chargedFailure_unique Verdict.intent_determined

end Minidregg.Kernel.ObjectiveActivityReceiver
