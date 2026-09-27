/-
Pure ordering for one locally observed fn consumer. This is not an admission
certificate: only NativeHostReplay may fold these transitions after admitting
each original Mini record and pairing it with that walk's original receipt.
Legacy empty-page records are recognized as historical anchors, without
claiming they enforced this ordering when first accepted.
-/
import Kernel.FnConsumerScope
import Kernel.DurableDataIntent

namespace Minidregg.Kernel.FnConsumerFrontierCore

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel

set_option autoImplicit false

structure Key where
  application : List UInt8
  scope : FnConsumerScope.Scope
  controlBinding : List UInt8
  gatewaySubject : SubjectId
  gatewayTarget : Nat
  gatewayCapability : CapabilityId
  deriving DecidableEq, Repr

/-- Durable consumer identity is independent of the gateway signing grant.
A grant rotation cannot mint a second registration for the same fn scope and
control namespace; it requires an explicit migration or new registration. -/
structure Namespace where
  application : List UInt8
  scope : FnConsumerScope.Scope
  controlBinding : List UInt8
  deriving DecidableEq, Repr

def Key.namespace (key : Key) : Namespace :=
  ⟨key.application, key.scope, key.controlBinding⟩

def namespaceStream : StreamCodec Namespace :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product FnConsumerScope.scopeStream bytesStream))
    (fun value => (value.application, value.scope, value.controlBinding))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩)
    (by intro value; cases value; rfl)

def namespaceNullifier (domain semantics : Digest) (consumerNamespace : Namespace) :
    StableNullifier :=
  let bytes := (StreamCodec.product digestStream
    (StreamCodec.product digestStream namespaceStream)).encode
      (domain, semantics, consumerNamespace)
  { codecVersion := 20
    domain := domain
    nullifierId := (Sp800185Cshake256.hash
      "DREGG/FN/CONSUMER-NAMESPACE-CLAIM/v1".toUTF8.toList bytes).digest
    canonicalBytes := "DREGG/FN/CONSUMER-NAMESPACE-CLAIM/v1".toUTF8.toList ++ bytes }

def keyStream : StreamCodec Key :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product FnConsumerScope.scopeStream
        (StreamCodec.product bytesStream
          (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
            (StreamCodec.product StreamCodec.nat
              CredentialAuthorityEntryCodec.capabilityIdStream)))))
    (fun key => (key.application, key.scope, key.controlBinding,
      key.gatewaySubject, key.gatewayTarget, key.gatewayCapability))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
      wire.2.2.2.2.1, wire.2.2.2.2.2⟩)
    (by intro key; cases key; rfl)

/-- The same complete predecessor key is used by both new empty-page and
selected-article progress. Distinct successors from one tip share a nullifier. -/
def frontierKeyBytes (domain semantics : Digest) (key : Key)
    (fromPosition : Nat) (predecessor : Option NativeHostCodec.Receipt) : List UInt8 :=
  (StreamCodec.product digestStream
    (StreamCodec.product digestStream
      (StreamCodec.product keyStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.option NativeHostCodec.receiptStream))))).encode
    (domain, semantics, key, fromPosition, predecessor)

def frontierNullifier (domain semantics : Digest) (key : Key)
    (fromPosition : Nat) (predecessor : Option NativeHostCodec.Receipt) :
    StableNullifier :=
  let bytes := frontierKeyBytes domain semantics key fromPosition predecessor
  { codecVersion := 17
    domain := domain
    nullifierId := (Sp800185Cshake256.hash
      "DREGG/FN/CONSUMER-FRONTIER-NULLIFIER/v2".toUTF8.toList bytes).digest
    canonicalBytes := "DREGG/FN/CONSUMER-FRONTIER-NULLIFIER/v2".toUTF8.toList ++
      bytes }

/-- Hashes only the exact authenticated fn poll report bytes retained by Host.
It is local gateway testimony, not a remote completeness certificate. -/
def reportDigest (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/FN/CONSUMER-POLL-REPORT/v2".toUTF8.toList bytes).digest

/-- The projected source digest is separate from the report digest so an ACK
selector must bind both the retained report and the exact selected article. -/
def sourceDigest (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash
    "DREGG/FN/CONSUMER-PROJECTED-SOURCE/v2".toUTF8.toList bytes).digest

inductive Kind where
  | legacyEmpty
  | emptyV2
  | selectedV2
  deriving DecidableEq, Repr

/-- The receipt must come from the same native-admitted replay step as the
classified original record. A v2 transition names the exact prior receipt,
except that the first transition from the virgin zero frontier names none. -/
structure Transition where
  key : Key
  kind : Kind
  fromPosition : Nat
  toPosition : Nat
  selectedSequence : Option Nat
  predecessor : Option NativeHostCodec.Receipt
  receipt : NativeHostCodec.Receipt
  deriving DecidableEq, Repr

/-- Admission can check a prospective successor before the durable executor
has produced its four-field same-walk receipt. -/
structure Candidate where
  key : Key
  kind : Kind
  fromPosition : Nat
  toPosition : Nat
  selectedSequence : Option Nat
  predecessor : Option NativeHostCodec.Receipt
  deriving DecidableEq, Repr

def Transition.candidate (transition : Transition) : Candidate :=
  ⟨transition.key, transition.kind, transition.fromPosition,
    transition.toPosition, transition.selectedSequence, transition.predecessor⟩

inductive Mode where
  | virgin
  | legacyAnchor
  | orderedV2
  deriving DecidableEq, Repr

structure Cursor where
  position : Nat
  receipt : Option NativeHostCodec.Receipt
  mode : Mode
  deriving DecidableEq, Repr

abbrev State := List (Key × Cursor)

def initial : Cursor := ⟨0, none, .virgin⟩

def lookup (state : State) (key : Key) : Cursor :=
  (state.find? (fun entry => entry.1 == key)).map Prod.snd |>.getD initial

/-- This is a pure predecessor check. Only the verifier-minted frontier may
supply `prior` for a live receiver; an arbitrary caller Cursor is not history
authority. -/
def checkAfter (prior : Cursor) (candidate : Candidate) : Except String Unit := do
  unless candidate.fromPosition == prior.position &&
      candidate.fromPosition < candidate.toPosition &&
      candidate.toPosition ≤ candidate.fromPosition + FnConsumerScope.maxPollScan &&
      candidate.toPosition ≤ 4294967295 do
    throw "fn consumer progress predecessor or scan window differs"
  match candidate.kind with
  | .legacyEmpty =>
      unless prior.mode != .orderedV2 && candidate.predecessor.isNone &&
          candidate.selectedSequence.isNone do
        throw "legacy empty-page progress cannot follow ordered progress"
  | .emptyV2 =>
      unless candidate.predecessor == prior.receipt &&
          candidate.selectedSequence.isNone do
        throw "fn consumer progress receipt predecessor differs"
  | .selectedV2 =>
      unless candidate.predecessor == prior.receipt &&
          candidate.selectedSequence.any (fun sequence =>
            candidate.fromPosition ≤ sequence && sequence + 1 == candidate.toPosition) do
        throw "fn selected progress sequence or receipt predecessor differs"
  pure ()

/-- The replay walk supplies `Transition` only after admitting the exact
original Mini record and pairing it with that walk's four-field receipt. -/
def step (state : State) (transition : Transition) : Except String State := do
  let prior := lookup state transition.key
  checkAfter prior transition.candidate
  let next : Cursor :=
    ⟨transition.toPosition, some transition.receipt,
      if transition.kind == .legacyEmpty then .legacyAnchor else .orderedV2⟩
  pure ((transition.key, next) :: state.filter (fun entry => entry.1 != transition.key))

end Minidregg.Kernel.FnConsumerFrontierCore
