import Kernel.ReactiveTerminalCell

namespace Minidregg.Scripts.ProbeReactiveTerminalCodec

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ReactiveTerminalCell
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def customization : List UInt8 :=
  "MINIDREGG.REACTIVE.TERMINAL/v2".toUTF8.toList

/-- The probe uses the deployed-shape 256-bit cSHAKE digest, not the old
length-root witness. -/
def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash customization bytes).digest

def zeroCharge : Charge := fun _ => 0

def openCell : OpenCell where
  codecVersion := wireVersion
  domain := ⟨10⟩
  promiseId := ⟨11⟩
  deadline := 7
  transactionId := ⟨12⟩
  nullifierId := ⟨13⟩
  eventId := ⟨14⟩
  terminalCell := ⟨20⟩
  outboxCell := ⟨21⟩
  clockCell := ⟨22⟩
  triggerCell := ⟨23⟩
  openTerminalBytes := [82, 84, 67, 47, 79, 80, 69, 78]
  openOutboxBytes := [82, 84, 67, 47, 79, 85, 84, 66, 79, 88]
  exactCharge := zeroCharge
  terminalOutboxDistinct := by decide
  terminalClockDistinct := by decide
  outboxClockDistinct := by decide
  terminalTriggerDistinct := by decide
  outboxTriggerDistinct := by decide

def evidenceBytes : List UInt8 :=
  "provider evidence over a real 256-bit root".toUTF8.toList

def triggerBytes : List UInt8 :=
  "semantic trigger image v2".toUTF8.toList

def finalizePlan : Plan rootBytes openCell where
  settledAt := 7
  decision := .finalize (by decide)
  evidenceRoot := rootBytes evidenceBytes
  triggerRoot := rootBytes triggerBytes

def cancelPlan : Plan rootBytes openCell where
  settledAt := 7
  decision := .cancel (by decide)
  evidenceRoot := rootBytes
    "conflicting cancellation evidence".toUTF8.toList
  triggerRoot := rootBytes triggerBytes

def beforeBytes (cellId : CellId) : List UInt8 :=
  if cellId = openCell.terminalCell then openCell.openTerminalBytes
  else if cellId = openCell.outboxCell then openCell.openOutboxBytes
  else if cellId = openCell.clockCell then finalizePlan.clockBytes
  else if cellId = openCell.triggerCell then triggerBytes
  else []

def snapshotFrom (bytesAt : CellId → List UInt8) : DataSnapshot rootBytes where
  model :=
    { roots := fun cellId => rootBytes (bytesAt cellId)
      consumed := fun _ => false
      available := fun _ => 100
      history := []
      journal := [] }
  canonicalBytes := bytesAt
  coherent := fun _ => rfl

def before : DataSnapshot rootBytes := snapshotFrom beforeBytes

def wrongClockBytes (cellId : CellId) : List UInt8 :=
  if cellId = openCell.clockCell then finalizePlan.clockBytes ++ [0]
  else beforeBytes cellId

def wrongTriggerBytes (cellId : CellId) : List UInt8 :=
  if cellId = openCell.triggerCell then triggerBytes ++ [0]
  else beforeBytes cellId

def accepted : Outcome rootBytes → Bool
  | .accepted _ => true
  | _ => false

def replayed : Outcome rootBytes → Bool
  | .replayed _ => true
  | _ => false

def transactionConflict : Outcome rootBytes → Bool
  | .rejected (.durable .transactionConflict) => true
  | _ => false

def staleReadGuard : Outcome rootBytes → Bool
  | .rejected .staleReadGuard => true
  | _ => false

def require (label : String) (condition : Bool) : IO Unit :=
  if condition then IO.println s!"PASS {label}"
  else throw <| IO.userError s!"FAIL {label}"

def boundedPayloads : Bool :=
  finalizePlan.clockBytes.length ≤ 64 &&
  finalizePlan.outboxBytes.length ≤ 192 &&
  finalizePlan.terminalBytes.length ≤ 256 &&
  finalizePlan.settlementEvent.canonicalBytes.length ≤ 384 &&
  finalizePlan.nullifier.canonicalBytes.length ≤ 96

def main : IO Unit := do
  let generic : FramedFields :=
    { kind := 200
      fields := [[1, 2, 3], encodeDigest (rootBytes evidenceBytes), []] }
  let encoded := framedFieldsCodec.encode generic
  require "V2 generic frame decodes with full consumption"
    (decide (decodeFrame encoded = some generic))
  require "trailing bytes are rejected"
    (decide (decodeFrame (encoded ++ [0]) = none))
  require "accepted frame re-encodes exactly"
    (match decodeFrame encoded with
      | some framed => decide (frame framed.kind framed.fields = encoded)
      | none => false)
  require "terminal alternatives remain byte-distinct"
    (decide (finalizePlan.terminalBytes ≠ cancelPlan.terminalBytes))
  require "actual cSHAKE payloads stay bounded" boundedPayloads

  let committed := execute .complete before finalizePlan.intent
  let installed := DataSnapshot.install before finalizePlan.intent
  require "existing terminal DataIntent commits" (accepted committed)
  require "exact retry replays"
    (replayed (execute .complete installed finalizePlan.intent))
  require "conflicting terminal choice is refused"
    (transactionConflict (execute .complete installed cancelPlan.intent))
  require "wrong clock root is refused"
    (staleReadGuard (execute .complete
      (snapshotFrom wrongClockBytes) finalizePlan.intent))
  require "wrong trigger root is refused"
    (staleReadGuard (execute .complete
      (snapshotFrom wrongTriggerBytes) finalizePlan.intent))

  IO.println s!"terminal-bytes={finalizePlan.terminalBytes.length} \
outbox-bytes={finalizePlan.outboxBytes.length} \
event-bytes={finalizePlan.settlementEvent.canonicalBytes.length} \
nullifier-bytes={finalizePlan.nullifier.canonicalBytes.length}"
  IO.println s!"terminal-root={finalizePlan.terminalRoot.value}"

end Minidregg.Scripts.ProbeReactiveTerminalCodec

def main : IO Unit :=
  Minidregg.Scripts.ProbeReactiveTerminalCodec.main
