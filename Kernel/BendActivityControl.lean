/- Protected Activity facet over actual Mini snapshots/intents. Ordinary content
writes cannot inject arbitrary canonical checkpoints. The typed advance path
checks exact predecessor bytes, reexecutes actual Bend run, and carries a stable
native nullifier. It must compose with every other protected-controller gate.
Native current-authority admission and Appended readback remain separate joins.
-/
import Kernel.BendActivity
import Compiler.ContentControlFrame

namespace Minidregg.Kernel.BendActivityControl
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.BendClosureMachine
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.BendClosureContinuationCodec
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
set_option autoImplicit false

abbrev Pin := ContentControlFrame.Pin

def readRecord (pin : Pin) (bytes : List UInt8) : Option BendActivity.Record := do
  let payload ← ContentControlFrame.readPayload pin bytes
  BendActivity.decode payload

inductive Phase | absent | bare | initialized deriving DecidableEq, BEq

/-- Native content birth is neutral. Activity initialization is a second,
protected current-authority operation, not an invented atomic birth+edit. -/
def phase (pin : Pin) (bytes : List UInt8) : Option Phase := do
  let image ← (ResourceBirthCodec.LifecycleImage.codec CanonicalCellRegistry.registry).decode bytes
  match image with
  | .fresh => some .absent
  | .retired => none
  | .live packed => match packed with
    | ⟨.content, content⟩ =>
      if (readRecord pin bytes).isSome then some .initialized
      else if CanonicalCellRegistry.UserShape .content content.logical then some .bare else none
    | _ => none

/-- Source pin plus exact predecessor Activity bytes form the claim identity;
no hash injectivity is assumed and the bytes survive native replay equality. -/
def claimBytes (pin : Pin) (before : BendActivity.Record) : List UInt8 :=
  "DREGG.BEND.ACTIVITY.CONSUME/v1".toUTF8.toList ++
    ContentControlFrame.pinStream.encode pin ++ BendActivity.encode before

def claim (rootBytes : List UInt8 → Digest) (pin : Pin)
    (before : BendActivity.Record) : StableNullifier :=
  {codecVersion := 1, domain := pin.schema,
    nullifierId := rootBytes (claimBytes pin before), canonicalBytes := claimBytes pin before}

/-- Appending this restrictive claim does not remove guards, native payloads,
charges or authority checks. The Activity native adapter must reconstruct it in
live admission AND replay of the same typed operation. -/
def withClaim {rootBytes : List UInt8 → Digest} (pin : Pin)
    (before : BendActivity.Record) (intent : DataIntent rootBytes) : DataIntent rootBytes :=
  {intent with nullifiers := claim rootBytes pin before :: intent.nullifiers}

def ordinaryGate {rootBytes : List UInt8 → Digest} (pin : Pin)
    (_snapshot : DataSnapshot rootBytes) (intent : DataIntent rootBytes) :
    Except RejectReason Unit :=
  if intent.writes.any (fun write => write.cellId == pin.cell)
  then .error (.durable .transactionConflict) else .ok ()

/-- A new protected coordinate can only originate in the actual machine start.
Freshness is exact lifecycle bytes; native birth authority and its guarded
installation are still required. An arbitrary existing checkpoint cannot be
promoted to a rooted Activity merely because it decodes. -/
structure CheckedBirth {rootBytes : List UInt8 → Digest}
    (pin : Pin) (binding : List UInt8) (generation : Nat) (limits : Limits)
    (library : Library) (entry : Nat)
    (snapshot : DataSnapshot rootBytes) (intent : DataIntent rootBytes) where
  private mk ::
  initial : BendActivity.Record
  fresh : snapshot.canonicalBytes pin.cell = []
  actual : BendActivity.start binding generation limits library entry = .ok initial
  post : ∃ write, write ∈ intent.writes ∧ write.cellId = pin.cell ∧
    ContentControlFrame.readPayload pin write.canonicalPostBytes = some (BendActivity.encode initial)

def checkBirth {rootBytes : List UInt8 → Digest} (pin : Pin)
    (binding : List UInt8) (generation : Nat) (limits : Limits)
    (library : Library) (entry : Nat)
    (snapshot : DataSnapshot rootBytes) (intent : DataIntent rootBytes) :
    Option (CheckedBirth pin binding generation limits library entry snapshot intent) := do
  if fresh : snapshot.canonicalBytes pin.cell = [] then
    match actual : BendActivity.start binding generation limits library entry with
    | .error _ => none
    | .ok initial =>
      if post : intent.writes.any (fun write => decide (write.cellId = pin.cell ∧
          ContentControlFrame.readPayload pin write.canonicalPostBytes = some (BendActivity.encode initial))) then
        some ⟨initial, fresh, actual, by
          simpa only [List.any_eq_true, decide_eq_true_eq] using post⟩
      else none
  else none

/-- A birth witness carries actual initialization, never a decode-only premise. -/
theorem checked_birth_actual {rootBytes : List UInt8 → Digest}
    {pin : Pin} {binding : List UInt8} {generation : Nat} {limits : Limits}
    {library : Library} {entry : Nat} {snapshot : DataSnapshot rootBytes}
    {intent : DataIntent rootBytes}
    (checked : CheckedBirth pin binding generation limits library entry snapshot intent) :
    BendActivity.start binding generation limits library entry = .ok checked.initial :=
  checked.actual

/-- Actual ordinary content birth precedes this initializer. The protected
bare phase contains no arbitrary machine checkpoint and can only install start. -/
structure CheckedInitialize {rootBytes : List UInt8 → Digest}
    (pin : Pin) (binding : List UInt8) (generation : Nat) (limits : Limits)
    (library : Library) (entry : Nat)
    (snapshot : DataSnapshot rootBytes) (intent : DataIntent rootBytes) where
  private mk ::
  initial : BendActivity.Record
  bare : phase pin (snapshot.canonicalBytes pin.cell) = some .bare
  actual : BendActivity.start binding generation limits library entry = .ok initial
  post : ∃ write, write ∈ intent.writes ∧ write.cellId = pin.cell ∧
    ContentControlFrame.readPayload pin write.canonicalPostBytes = some (BendActivity.encode initial)

def checkInitialize {rootBytes : List UInt8 → Digest} (pin : Pin)
    (binding : List UInt8) (generation : Nat) (limits : Limits)
    (library : Library) (entry : Nat)
    (snapshot : DataSnapshot rootBytes) (intent : DataIntent rootBytes) :
    Option (CheckedInitialize pin binding generation limits library entry snapshot intent) := do
  if bare : phase pin (snapshot.canonicalBytes pin.cell) = some .bare then
    match actual : BendActivity.start binding generation limits library entry with
    | .error _ => none
    | .ok initial =>
      if post : intent.writes.any (fun write => decide (write.cellId = pin.cell ∧
          ContentControlFrame.readPayload pin write.canonicalPostBytes = some (BendActivity.encode initial))) then
        some ⟨initial, bare, actual, by
          simpa only [List.any_eq_true, decide_eq_true_eq] using post⟩
      else none
  else none

/-- Exact state provenance, not a claim of native authority. A receiving adapter
must pair this with actual current source admission and ordinary gates for all
OTHER facets before it may install this full intent. -/
structure CheckedAdvance {rootBytes : List UInt8 → Digest}
    (pin : Pin) (limits : Limits) (library : Library) (ticks : Nat)
    (snapshot : DataSnapshot rootBytes) (intent : DataIntent rootBytes) where
  private mk ::
  before : BendActivity.Record
  after : BendActivity.Record
  current : readRecord pin (snapshot.canonicalBytes pin.cell) = some before
  actual : BendActivity.advance limits library ticks before = some after
  carries : claim rootBytes pin before ∈ intent.nullifiers
  post : ∃ write, write ∈ intent.writes ∧ write.cellId = pin.cell ∧
    ContentControlFrame.readPayload pin write.canonicalPostBytes = some (BendActivity.encode after)

/-- The caller supplies current source-selected context and predecessor, never
an alleged post-state. Proposed post bytes must equal the recomputed successor.
This is a pure admission helper, not an effect dispatcher or store implementation. -/
def checkAdvance {rootBytes : List UInt8 → Digest} (pin : Pin)
    (binding : List UInt8) (limits : Limits) (library : Library) (ticks : Nat)
    (generation ordinal : Nat) (preimage : List UInt8)
    (snapshot : DataSnapshot rootBytes) (intent : DataIntent rootBytes) :
    Option (CheckedAdvance pin limits library ticks snapshot intent) := do
  if snapshot.canonicalBytes pin.cell != preimage then none else do
    match current : readRecord pin (snapshot.canonicalBytes pin.cell) with
    | none => none
    | some before =>
      if before.checkpoint.contextBytes != encodeContext (executionContext binding limits library) ||
          before.checkpoint.generation != generation || before.ordinal != ordinal then none else do
        match actual : BendActivity.advance limits library ticks before with
        | none => none
        | some after =>
          if carries : claim rootBytes pin before ∈ intent.nullifiers then
            if post : intent.writes.any (fun write => decide (write.cellId = pin.cell ∧
                ContentControlFrame.readPayload pin write.canonicalPostBytes = some (BendActivity.encode after))) then
              some ⟨before, after, current, actual, carries, by
                simpa only [List.any_eq_true, decide_eq_true_eq] using post⟩
            else none
          else none

/-- Actual accepted tick proposals cannot substitute a worker-selected state. -/
theorem checked_advance_actual {rootBytes : List UInt8 → Digest}
    {pin : Pin} {limits : Limits} {library : Library} {ticks : Nat}
    {snapshot : DataSnapshot rootBytes} {intent : DataIntent rootBytes}
    (checked : CheckedAdvance pin limits library ticks snapshot intent) :
    checked.after.checkpoint.state = run limits library ticks checked.before.checkpoint.state :=
  (BendActivity.advance_actual_run checked.actual).1

/-- The existing native installer consumes the exact activity-predecessor claim.
Replaying that claim as a NEW admission is refused. Existing same-id retry keeps
its original durable outcome through the original durable protocol. -/
theorem installed_claim_refuses_new_admission {rootBytes : List UInt8 → Digest}
    {pin : Pin} {limits : Limits} {library : Library} {ticks : Nat}
    {snapshot : DataSnapshot rootBytes} {intent : DataIntent rootBytes}
    (checked : CheckedAdvance pin limits library ticks snapshot intent)
    (later : DataIntent rootBytes)
    (sameClaim : claim rootBytes pin checked.before ∈ later.nullifiers) :
    later.preflight (DataSnapshot.install snapshot intent) ≠ .ok () := by
  apply DataIntent.consumed_nullifier_refused _ later _ sameClaim
  change (DurableCommitProtocol.Snapshot.install snapshot.model intent.erase).consumed
    (claim rootBytes pin checked.before) = true
  exact DurableCommitProtocol.Snapshot.install_consumes snapshot.model intent.erase _ checked.carries

#assert_axioms checked_birth_actual
#assert_axioms checked_advance_actual
#assert_axioms installed_claim_refuses_new_admission
end Minidregg.Kernel.BendActivityControl
