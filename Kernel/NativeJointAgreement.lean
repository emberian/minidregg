/- Internal durable agreement seam. This is NOT a network certificate verifier or
an implementation of Generic Simplex. It supplies exact replay, persist-before-
emit, uncertain-reply handling and the protocol-owned local voting journal for
that implementation. Raw JournalEvent is controller-internal, never user ingress.

The complete baseline is Generic Simplex arXiv:2609.32985v1 Figures 1/4/5 and
Appendix C. Both READY rules, active-view continuation and outer-view timeout
logic remain required; this module does not replace them with a quorum slogan.
-/
import Kernel.JointReservation

namespace Minidregg.Kernel.NativeJointAgreement

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.JointInvocationCandidate
open Minidregg.Kernel.JointDecisionRecovery

set_option autoImplicit false

/-- Internal tags: 0 YES, 1 NO, 2 retained recovery, 3 exact physical Applied,
4 semantic close, 5 handoff. Payload is canonical and interpreted by its tag. -/
structure JournalEvent where
  tag : Nat
  index : Nat
  payload : List UInt8
  deriving DecidableEq, Repr

def eventStream : StreamCodec JournalEvent :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat bytesStream))
    (fun e => (e.tag, e.index, e.payload))
    (fun (t, i, p) => ⟨t, i, p⟩) (by intro e; cases e; rfl)

def phaseTag : RecoveryPhase → Nat
  | .collecting => 0 | .installing => 1 | .releasing => 2 | .complete => 3

def phaseOfTag : Nat → RecoveryPhase
  | 0 => .collecting | 1 => .installing | 2 => .releasing | _ => .complete

def recoveryStream : StreamCodec RecoveryJob :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product (StreamCodec.list bytesStream)
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))
    (fun j => (j.accessCapability, j.opaqueParticipantMask, j.evidence,
      j.originFence, phaseTag j.phase, j.sequence))
    (fun (a, m, e, f, p, s) => ⟨a, m, e, f, phaseOfTag p, s⟩)
    (by intro j; cases j with | mk a m e f p s => cases p <;> rfl)

/-- Canonical decoding rejects unknown phase aliases and trailing bytes. -/
def decodeRecovery (bytes : List UInt8) : Option RecoveryJob := do
  let job ← recoveryStream.toLawful.decode bytes
  if recoveryStream.encode job = bytes then some job else none

@[simp] theorem decodeRecovery_encode (job : RecoveryJob) :
    decodeRecovery (recoveryStream.encode job) = some job := by
  have roundtrip := recoveryStream.toLawful.decode_encode job
  change recoveryStream.toLawful.decode (recoveryStream.encode job) = some job at roundtrip
  simp [decodeRecovery, roundtrip]

/-- Applies already-admitted local finality/physical-install facts. Source
admission and verification are not inferred from opaque evidence bytes here. -/
def applyEvent {Custody : Type} {plan : Plan Custody} (s : State plan)
    (event : JournalEvent) : Option (State plan) :=
  match event.tag with
  | 0 | 1 =>
      if hi : event.index < plan.candidate.participants.length then
        decideVote s ⟨event.index, hi⟩ (if event.tag = 0 then .yes else .no) event.payload
      else none
  | 2 => do
      if event.index ≠ 0 then none else
        let job ← decodeRecovery event.payload
        retainRecovery s job
  | 3 =>
      if hi : event.index < plan.candidate.participants.length then
        if event.payload = [] then recordApplied s ⟨event.index, hi⟩ else none
      else none
  | 4 => if event.index = 0 ∧ event.payload = [] then some (close s) else none
  | 5 => if event.payload = [] then handoff s event.index else none
  | _ => none

def replay {Custody : Type} {plan : Plan Custody} (s : State plan) :
    List JournalEvent → Option (State plan)
  | [] => some s
  | e :: rest => do
      let next ← applyEvent s e
      replay next rest

theorem replay_append {Custody : Type} {plan : Plan Custody}
    (s : State plan) (left right : List JournalEvent) :
    replay s (left ++ right) = (replay s left).bind (fun t => replay t right) := by
  induction left generalizing s with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, replay]
      cases h : applyEvent s e with
      | none => simp
      | some t => simpa [h] using ih t

/-- The durable frame binds exact candidate bytes to its entire local journal.
A different candidate cannot reuse the same sequence by merely colliding hashes. -/
structure Journal where
  candidateBytes : List UInt8
  initialEpoch : Nat
  events : List JournalEvent
  pendingOutbox : List (List UInt8)
  deriving DecidableEq, Repr

def journalStream : StreamCodec Journal :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product (StreamCodec.list eventStream) (StreamCodec.list bytesStream))))
    (fun j => (j.candidateBytes, j.initialEpoch, j.events, j.pendingOutbox))
    (fun (c, e, xs, outbox) => ⟨c, e, xs, outbox⟩) (by intro j; cases j; rfl)

def restore {Custody : Type} (codec : StreamCodec Custody) (plan : Plan Custody)
    (journal : Journal) : Option (State plan) :=
  if journal.candidateBytes = (candidateStream codec).encode plan.candidate then
    replay (initial plan journal.initialEpoch) journal.events
  else none

theorem restore_wrong_candidate {Custody : Type} (codec : StreamCodec Custody)
    (plan : Plan Custody) (journal : Journal)
    (wrong : journal.candidateBytes ≠ (candidateStream codec).encode plan.candidate) :
    restore codec plan journal = none := by simp [restore, wrong]

/-- The exact restart frame includes messages not yet safely retired. Re-emission
is a protocol retransmission, never permission to retry an application effect. -/
theorem journal_encode_injective : Function.Injective journalStream.encode := by
  intro a b equal
  have left := journalStream.toLawful.decode_encode a
  have right := journalStream.toLawful.decode_encode b
  change journalStream.toLawful.decode (journalStream.encode a) = some a at left
  change journalStream.toLawful.decode (journalStream.encode b) = some b at right
  have decoded := congrArg journalStream.toLawful.decode equal
  rw [left, right] at decoded
  exact Option.some.inj decoded

/-- A dedicated protected journal transport. CAS compares the expected full
prior frame. Physical implementation must durably flush before reporting success.
Existing DurableReceiverIO CasObservation preserves uncertain outcomes. -/
structure Transport where
  compareAppend : List UInt8 → List UInt8 → IO DurableReceiverIO.CasObservation
  read : IO (Except String (List UInt8))
  emit : List UInt8 → IO Unit

inductive SubmitResult where
  | durable (journal : Journal)
  | refused
  | conflict
  | uncertain (detail : String)

/-- Admission is an upstream controller obligation. Even Installed/AlreadyPresent
must be read back exactly before any outbound bytes are emitted. An unknown
outcome does not trigger a second mutation or fabricate a finality certificate. -/
def persistThenEmit {Custody : Type} (codec : StreamCodec Custody) (plan : Plan Custody)
    (transport : Transport) (before : Journal) (event : JournalEvent)
    (outbound : List (List UInt8)) : IO SubmitResult := do
  let some state := restore codec plan before | return .refused
  let some _ := applyEvent state event | return .refused
  let after := { before with events := before.events ++ [event]
                             pendingOutbox := before.pendingOutbox ++ outbound }
  let bytes := journalStream.encode after
  match ← transport.compareAppend (journalStream.encode before) bytes with
  | .conflict => return .conflict
  | .uncertain detail => return .uncertain detail
  | .installed | .alreadyPresent =>
      match ← transport.read with
      | .error detail => return .uncertain detail
      | .ok actual =>
          if actual = bytes then
            try
              for message in after.pendingOutbox do transport.emit message
              return .durable after
            catch error =>
              return .uncertain ("journal durable; outbox retained: " ++ error.toString)
          else return .uncertain "joint journal readback differs; recover before retry"

/- The Simplex local safety journal is separate from semantic application slots.
Neither a private-channel vote nor a local COMMIT send is a portable YES cert. -/
structure ViewJournal where
  view : Nat
  voted : Option (List UInt8)
  disableRequested : Bool
  committed : Option (List UInt8)
  readyCoreSent : Bool
  readyRelaySent : Bool
  deriving DecidableEq, Repr

def recordVote (s : ViewJournal) (value : List UInt8) : Option ViewJournal :=
  if s.disableRequested || s.voted.isSome then none
  else some { s with voted := some value }

def requestDisable (s : ViewJournal) : Option ViewJournal :=
  if s.committed.isSome then none else some { s with disableRequested := true }

/-- Both paper rules have separate persisted send bits. Coalescing them requires
an additional implementation refinement and is not silently assumed here. -/
def recordReady (s : ViewJournal) (relay : Bool) : Option ViewJournal :=
  if relay then
    if s.readyRelaySent then none else some { s with readyRelaySent := true }
  else
    if s.readyCoreSent then none else some { s with readyCoreSent := true }

theorem disabled_cannot_vote (s : ViewJournal) (value : List UInt8)
    (disabled : s.disableRequested = true) : recordVote s value = none := by
  simp [recordVote, disabled]

theorem vote_once (s t : ViewJournal) (first second : List UInt8)
    (step : recordVote s first = some t) : recordVote t second = none := by
  unfold recordVote at step
  split at step
  · cases step
  · cases Option.some.inj step
    simp [recordVote]

end Minidregg.Kernel.NativeJointAgreement
