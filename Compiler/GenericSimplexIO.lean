module

public import Compiler.GenericSimplexCodec
public import Kernel.GenericSimplexStructure
public import Kernel.GenericSimplexRelativeSelf
public import Theory.AssertAxioms

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

namespace Minidregg.Compiler.GenericSimplexIO
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexRelative
set_option autoImplicit false
/-- Persisted inputs include source-validation grants, so replay never rechecks
them against a different present snapshot. This log is private trusted storage.
A source check can be appended only by the native controller, not peer ingress.
An event is an encoded `Entry`: an input of the running replica (`Replica.step`, blocks
relative to its committed height), or an acknowledgement that drains its outputs. Replay
starts at `snapshot` when present (a checkpoint), else at `Replica.start`. -/
structure Journal where
  context : Context
  self : Nat
  initialTime : Nat
  events : List Event := []
  commitWitnesses : List CommitWitness := []
  snapshot : Option Replica := none
  deriving DecidableEq, BEq, Repr
def journalStream : StreamCodec Journal :=
  StreamCodec.xmap
    (StreamCodec.product contextStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product (StreamCodec.list eventStream)
          (StreamCodec.product (StreamCodec.list commitWitnessStream) (StreamCodec.option replicaStream))))))
    (fun j => (j.context,j.self,j.initialTime,j.events,j.commitWitnesses,j.snapshot))
    (fun (c,s,t,e,w,n) => ⟨c,s,t,e,w,n⟩) (by intro j; cases j; rfl)
/-- One journal entry applied to the running replica. -/
def applyEntry (c : Config) (h : ChainDigest) (r : Replica) : Entry → Replica
  | .input input => r.step c h input
  | .flush sends owed => r.flush sends owed
  | .consume count => r.consume count
def replayEvents (c : Config) (h : ChainDigest) : Replica → List Event → Option Replica
  | r, [] => some r
  | r, e :: es => do
      let entry ← decodeEntry e
      let next := applyEntry c h r entry
      if next.core.failed then none else replayEvents c h next es
/-- An entry never changes whose replica it is (`GenericSimplexRelativeSelf.step_self`). -/
theorem applyEntry_self (c : Config) (h : ChainDigest) (r : Replica) (entry : Entry) :
    (applyEntry c h r entry).core.self = r.core.self := by
  cases entry with
  | input input => exact Minidregg.Kernel.GenericSimplexRelativeSelf.step_self c h r input
  | flush sends owed => rfl
  | consume count => rfl
/-- **A replay is of one replica**: whatever the events, the replayed replica is the member
the replay started from, and it has not failed if that one had not. No identity is compared
while a journal is replayed or appended to. -/
theorem replayEvents_kept (c : Config) (h : ChainDigest) :
    ∀ (events : List Event) (r s : Replica), replayEvents c h r events = some s →
      s.core.self = r.core.self ∧ (r.core.failed = false → s.core.failed = false)
  | [], r, s, done => by
    have same : r = s := by simpa [replayEvents] using done
    subst same
    exact ⟨rfl,id⟩
  | e :: es, r, s, done => by
    cases decoded : decodeEntry e with
    | none => simp [replayEvents, decoded] at done
    | some entry =>
      have step : replayEvents c h r (e :: es) =
          if (applyEntry c h r entry).core.failed then none
          else replayEvents c h (applyEntry c h r entry) es := by
        simp [replayEvents, decoded]
      rw [step] at done
      split at done
      · simp at done
      · rename_i alive
        obtain ⟨sameSelf,keeps⟩ := replayEvents_kept c h es _ s done
        exact ⟨sameSelf.trans (applyEntry_self c h r entry),fun _ => keeps (by simpa using alive)⟩
theorem replayEvents_self {c : Config} {h : ChainDigest} {events : List Event} {r s : Replica}
    (done : replayEvents c h r events = some s) : s.core.self = r.core.self :=
  (replayEvents_kept c h events r s done).1
theorem replay_append (config : Config) (h : ChainDigest) (state : Replica) (events more : List Event) :
    replayEvents config h state (events ++ more) =
      (replayEvents config h state events).bind (fun next => replayEvents config h next more) := by
  induction events generalizing state with
  | nil => rfl
  | cons event events ih =>
    simp only [List.cons_append,replayEvents]
    cases decoded : decodeEntry event with
    | none => simp [decoded]
    | some input =>
      dsimp only [Bind.bind, Option.bind]
      split <;> simp_all <;> rfl

#assert_axioms replay_append

/-! ## Append-only physical journal

The durable image is `logMagic`, one length-prefixed canonical base `Journal`
frame, then length-prefixed `Delta` frames. Each acknowledged input is exactly
one appended delta. The only rewrite is a checkpoint, an atomic replacement by
one base frame carrying the replayed state (`checkpoint`); the writer keeps
the replaced image as the previous segment. A legacy whole-image
`agreement.bin` is not this shape and does not decode. -/

/-- ASCII "MINI-SIMPLEX-LOG" and a format version. The version also names the
`step` the inputs were recorded under, since a journal is replayed, not read:
version 2 = the timeout-backoff epoch (five-field `Config`); version 3 = the
quiescent-leader epoch (a leader proposes only with work); version 4 = the
base frame may carry a checkpoint snapshot (`Journal.snapshot`); version 5 = the
commit-floor epoch (`State.lastCommitted`: a view at or below the highest locally
committed view takes no further message, views below it drop their received messages,
and a replica at or below it enters the next view; the snapshot carries the field);
version 6 = the erasable-floor epoch (no rule acts in a view at or below the floor or
reads a view below it, a parent comes from the floor view or above, the floor keeps its
COMMIT evidence and serves it to a peer still at or below it, a replica stuck past its
timeout repeats itself, and the snapshot carries `floorEvidence`, `served`, `relay`);
version 7 = the retained epoch (`checked` keeps maximal source histories and `validBlock`
asks for a prefix of one, a committed payload leaves the offers, a view's timer runs only
with a reason to leave it (`wantsOut`), a message for a view above the horizon is not
stored and a repeated CANDIDATE(⊥) for a view its receiver has left is answered with the
receiver's own messages; the snapshot carries `ahead`);
version 8 = `ingest` takes a COMMIT for a view above the horizon (a quorum of them moves
the floor), and READY for one argument is sent once;
version 9 = `ingest` keeps at most `Config.cap` messages of one member and kind in a view
record;
version 10 = the COMMIT witnesses a journal keeps are signed over the chain's length and
running digest, not over the whole chain;
version 11 = the journal is the running replica's (`Replica.step`): an event is an encoded
`Entry` whose blocks are relative to the replica's committed height, the snapshot is a
`Replica`, the driver's drains are entries, a kept COMMIT witness is the statement and its
signature, and the digest is `chainDigest`'s 64 bytes (statement tag 4). An older log refuses
at this magic rather than being replayed under a different step or exported under a
different statement (`v10_log_refused`). -/
def logMagic : Bytes := [77,73,78,73,45,83,73,77,80,76,69,88,45,76,79,71,11]

/-- The magic of the previous format (inputs of `step` on whole chains). -/
def logMagicV10 : Bytes := [77,73,78,73,45,83,73,77,80,76,69,88,45,76,79,71,10]

/-- The format version byte of an image that carries the "MINI-SIMPLEX-LOG"
magic, whatever its version; `none` for anything else. Lets an open refuse an
older format by name instead of as a corrupt image. -/
def logFormatVersion (bytes : Bytes) : Option UInt8 :=
  if bytes.take logMagic.dropLast.length == logMagic.dropLast then
    bytes[logMagic.dropLast.length]? else none

/-- One acknowledged append: the exact entries replayed through `applyEntry`, and the
transferable COMMIT witnesses verified in the same transaction. -/
structure Delta where
  events : List Event := []
  witnesses : List CommitWitness := []
  deriving DecidableEq, BEq, Repr

def deltaStream : StreamCodec Delta :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.list eventStream) (StreamCodec.list commitWitnessStream))
    (fun d => (d.events,d.witnesses)) (fun (e,w) => ⟨e,w⟩) (by intro d; cases d; rfl)

def deltaFrame (d : Delta) : Bytes := bytesStream.encode (deltaStream.encode d)

def encodeDeltas : List Delta → Bytes
  | [] => []
  | d :: ds => deltaFrame d ++ encodeDeltas ds

/-- `recent` is newest-first so an append is O(1) in memory. -/
structure Log where
  base : Journal
  recent : List Delta := []
  deriving DecidableEq, BEq, Repr

def Log.deltas (l : Log) : List Delta := l.recent.reverse

def Log.encode (l : Log) : Bytes :=
  logMagic ++ bytesStream.encode (journalStream.encode l.base) ++ encodeDeltas l.deltas

def Log.push (l : Log) (d : Delta) : Log := {l with recent := d :: l.recent}

/-- The journal whose whole replay defines the state of this log. -/
def Log.merged (l : Log) : Journal :=
  { l.base with
    events := l.base.events ++ l.deltas.flatMap Delta.events
    commitWitnesses := l.base.commitWitnesses ++ l.deltas.flatMap Delta.witnesses }

def decodeDeltas : Nat → Bytes → Option (List Delta)
  | 0, bytes => if bytes.isEmpty then some [] else none
  | fuel + 1, bytes =>
    if bytes.isEmpty then some [] else do
      let (payload,rest) ← bytesStream.decodePrefix bytes
      let d ← deltaStream.toLawful.decode payload
      let ds ← decodeDeltas fuel rest
      some (d :: ds)

/-! A standing replica appends one frame per acknowledged input, so the frame
count of a journal is unbounded. The definitions above are the specification
the proofs use; the compiled code runs the loops below (`@[csimp]`), whose
stack use does not grow with the number of frames. -/

/-- Executable `encodeDeltas`: core's tail-recursive `flatMap`. -/
def encodeDeltasTR (ds : List Delta) : Bytes := ds.flatMap deltaFrame

@[csimp] theorem encodeDeltas_eq_encodeDeltasTR : @encodeDeltas = @encodeDeltasTR := by
  funext ds
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [encodeDeltas, encodeDeltasTR, ih]

/-- Executable `decodeDeltas`: one loop step per frame, decoded frames
accumulated newest-first. -/
def decodeDeltasLoop : Nat → Bytes → List Delta → Option (List Delta)
  | 0, bytes, acc => if bytes.isEmpty then some acc.reverse else none
  | fuel + 1, bytes, acc =>
    if bytes.isEmpty then some acc.reverse else
    match bytesStream.decodePrefix bytes with
    | none => none
    | some (payload,rest) =>
      match deltaStream.toLawful.decode payload with
      | none => none
      | some d => decodeDeltasLoop fuel rest (d :: acc)

def decodeDeltasTR (fuel : Nat) (bytes : Bytes) : Option (List Delta) :=
  decodeDeltasLoop fuel bytes []

theorem decodeDeltasLoop_eq (fuel : Nat) (bytes : Bytes) (acc : List Delta) :
    decodeDeltasLoop fuel bytes acc = (decodeDeltas fuel bytes).map (acc.reverse ++ ·) := by
  induction fuel generalizing bytes acc with
  | zero =>
    by_cases empty : bytes.isEmpty <;> simp [decodeDeltasLoop, decodeDeltas, empty]
  | succ fuel ih =>
    by_cases empty : bytes.isEmpty
    · simp [decodeDeltasLoop, decodeDeltas, empty]
    · cases framed : bytesStream.decodePrefix bytes with
      | none => simp [decodeDeltasLoop, decodeDeltas, empty, framed]
      | some split =>
        obtain ⟨payload,rest⟩ := split
        cases decoded : deltaStream.toLawful.decode payload with
        | none => simp [decodeDeltasLoop, decodeDeltas, empty, framed, decoded]
        | some d =>
          simp only [decodeDeltasLoop, decodeDeltas, empty, framed, decoded, ih,
            Bool.false_eq_true, ↓reduceIte]
          cases rested : decodeDeltas fuel rest <;> simp [decoded, rested]

@[csimp] theorem decodeDeltas_eq_decodeDeltasTR : @decodeDeltas = @decodeDeltasTR := by
  funext fuel bytes
  simp [decodeDeltasTR, decodeDeltasLoop_eq]

def decodeLog (bytes : Bytes) : Option Log := do
  if bytes.take logMagic.length != logMagic then none
  let (payload,rest) ← bytesStream.decodePrefix (bytes.drop logMagic.length)
  let base ← journalStream.toLawful.decode payload
  let deltas ← decodeDeltas rest.length rest
  some ⟨base,deltas.reverse⟩

/-- A version-10 log never decodes, whatever follows its magic: its inputs are whole-chain
inputs of `step` and its witnesses carry chains. -/
theorem v10_log_refused (rest : Bytes) : decodeLog (logMagicV10 ++ rest) = none := by
  have taken : (logMagicV10 ++ rest).take logMagic.length = logMagicV10 := rfl
  have differs : (logMagicV10 != logMagic) = true := by decide
  simp [decodeLog, taken, differs]

/-- It is still recognised as an agreement log of version 10, so an open names it. -/
theorem v10_log_named (rest : Bytes) : logFormatVersion (logMagicV10 ++ rest) = some 10 := by
  rfl

#assert_axioms v10_log_refused

/-- Replay of a decoded log over the merged journal: from its checkpoint snapshot if it has
one (which must be this replica's, and not failed), else from `Replica.start`. The result
must not have failed; that it is still this replica's is `replayLog_kept`, not a check. -/
def replayLog (expected : Context) (l : Log) : Option Replica :=
  let j := l.merged
  if (j.context != expected || !expected.wellFormed || decide (j.self ≥ expected.config.parties) ||
      !(j.snapshot.map fun n => n.core.self == j.self && !n.core.failed).getD true) = true
  then none
  else do
    let s ← replayEvents expected.config (chainDigest expected)
      (j.snapshot.getD (Replica.start expected.config (chainDigest expected) j.self j.initialTime)) j.events
    if s.core.failed then none else pure s

/-- **A replayed log is its own replica's, and has not failed.** The snapshot guard and
`start_self` fix whose replica the replay starts from; `replayEvents_kept` carries it. -/
theorem replayLog_kept {expected : Context} {l : Log} {s : Replica}
    (h : replayLog expected l = some s) : s.core.self = l.merged.self ∧ s.core.failed = false := by
  unfold replayLog at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i guard
    cases replayed : replayEvents expected.config (chainDigest expected)
        (l.merged.snapshot.getD (Replica.start expected.config (chainDigest expected) l.merged.self l.merged.initialTime))
        l.merged.events with
    | none => simp [replayed] at h
    | some t =>
      rw [replayed] at h
      change (if t.core.failed = true then none else pure t) = some s at h
      split at h
      · simp at h
      · rename_i alive
        have ts : t = s := by simpa [pure] using h
        subst ts
        refine ⟨?_,by simpa using alive⟩
        rw [replayEvents_self replayed]
        cases snap : l.merged.snapshot with
        | none =>
          exact Minidregg.Kernel.GenericSimplexRelativeSelf.start_self _ _ _ _
        | some n =>
          show n.core.self = l.merged.self
          exact Classical.byContradiction fun differs => guard (by simp [snap, differs])

/-- Whole canonical replay of the physical log bytes: `decodeLog` accepts only
encodings (`decodeLog_canonical`). -/
def restoreLog (expected : Context) (bytes : Bytes) : Option (Log × Replica) := do
  let l ← decodeLog bytes
  let s ← replayLog expected l
  some (l,s)

theorem bytesStream_encode_ne_nil (payload : Bytes) : bytesStream.encode payload ≠ [] := by
  simp [bytesStream, StreamCodec.nat, StreamCodec.encodeNat]

theorem encodeDeltas_append (ds : List Delta) (d : Delta) :
    encodeDeltas (ds ++ [d]) = encodeDeltas ds ++ deltaFrame d := by
  induction ds with
  | nil => simp [encodeDeltas]
  | cons x xs ih => simp [encodeDeltas, ih, List.append_assoc]

theorem length_le_encodeDeltas (ds : List Delta) : ds.length ≤ (encodeDeltas ds).length := by
  induction ds with
  | nil => simp [encodeDeltas]
  | cons d ds ih =>
    have nonempty : 0 < (deltaFrame d).length :=
      List.length_pos_of_ne_nil (bytesStream_encode_ne_nil _)
    simp only [encodeDeltas, List.length_append, List.length_cons]
    omega

theorem decodeDeltas_encode (ds : List Delta) :
    ∀ fuel, (encodeDeltas ds).length ≤ fuel → decodeDeltas fuel (encodeDeltas ds) = some ds := by
  induction ds with
  | nil => intro fuel _; cases fuel <;> simp [encodeDeltas, decodeDeltas]
  | cons d ds ih =>
    intro fuel bound
    have frame : (deltaFrame d) ≠ [] := bytesStream_encode_ne_nil _
    have frameLength : 0 < (deltaFrame d).length := List.length_pos_of_ne_nil frame
    have total : (encodeDeltas (d :: ds)).length = (deltaFrame d).length + (encodeDeltas ds).length := by
      simp [encodeDeltas]
    cases fuel with
    | zero => omega
    | succ fuel =>
      have rest := ih fuel (by omega)
      have payload := bytesStream.decodePrefix_encode (deltaStream.encode d) (encodeDeltas ds)
      have inner := deltaStream.toLawful.decode_encode d
      change deltaStream.toLawful.decode (deltaStream.encode d) = some d at inner
      have nonempty : (encodeDeltas (d :: ds)).isEmpty = false := by
        simp [encodeDeltas, deltaFrame, bytesStream_encode_ne_nil]
      simp only [decodeDeltas, nonempty, Bool.false_eq_true, ↓reduceIte]
      simp only [encodeDeltas, deltaFrame] at payload ⊢
      simp [payload, inner, rest]

theorem decodeLog_encode (l : Log) : decodeLog l.encode = some l := by
  have base := bytesStream.decodePrefix_encode (journalStream.encode l.base)
    (encodeDeltas l.recent.reverse)
  have inner : journalStream.toLawful.decode (journalStream.encode l.base) = some l.base :=
    journalStream.toLawful.decode_encode l.base
  have deltas : decodeDeltas (encodeDeltas l.recent.reverse).length
      (encodeDeltas l.recent.reverse) = some l.recent.reverse :=
    decodeDeltas_encode _ _ (Nat.le_refl _)
  unfold decodeLog Log.encode Log.deltas
  simp [List.append_assoc, List.take_left', List.drop_left', base, inner, deltas]

theorem encodeDeltas_decodeDeltas {fuel : Nat} {bytes : Bytes} {ds : List Delta}
    (decoded : decodeDeltas fuel bytes = some ds) : encodeDeltas ds = bytes := by
  induction fuel generalizing bytes ds with
  | zero =>
    by_cases empty : bytes.isEmpty
    · simp [decodeDeltas, empty] at decoded
      subst decoded
      simp [encodeDeltas, List.isEmpty_iff.mp empty]
    · simp [decodeDeltas, empty] at decoded
  | succ fuel ih =>
    by_cases empty : bytes.isEmpty
    · simp [decodeDeltas, empty] at decoded
      subst decoded
      simp [encodeDeltas, List.isEmpty_iff.mp empty]
    · cases framed : bytesStream.decodePrefix bytes with
      | none => simp [decodeDeltas, empty, framed] at decoded
      | some split =>
        obtain ⟨payload, rest⟩ := split
        cases delta : deltaStream.toLawful.decode payload with
        | none => simp [decodeDeltas, empty, framed, delta] at decoded
        | some d =>
          cases tail : decodeDeltas fuel rest with
          | none => simp [decodeDeltas, empty, framed, delta, tail] at decoded
          | some more =>
            simp [decodeDeltas, empty, framed, delta, tail] at decoded
            subst decoded
            simp only [encodeDeltas, deltaFrame, deltaStream.toLawful_canonical _ _ delta, ih tail]
            exact bytesStream.encode_decodePrefix _ _ _ framed

/-- The log decoder is canonical: every stream it reads is, the magic is
checked, and the delta frames are consumed to the end. -/
theorem decodeLog_canonical {bytes : Bytes} {l : Log}
    (decoded : decodeLog bytes = some l) : l.encode = bytes := by
  unfold decodeLog at decoded
  by_cases magic : (bytes.take logMagic.length != logMagic) = true
  · simp [magic] at decoded
  · have exact : bytes.take logMagic.length = logMagic := by simpa using magic
    simp only [magic, Bool.false_eq_true, ↓reduceIte] at decoded
    cases framed : bytesStream.decodePrefix (bytes.drop logMagic.length) with
    | none => simp [framed] at decoded
    | some split =>
      obtain ⟨payload, rest⟩ := split
      cases journal : journalStream.toLawful.decode payload with
      | none => simp [framed, journal] at decoded
      | some base =>
        cases deltas : decodeDeltas rest.length rest with
        | none => simp [framed, journal, deltas] at decoded
        | some ds =>
          simp [framed, journal, deltas] at decoded
          subst decoded
          have outer := bytesStream.encode_decodePrefix _ _ _ framed
          rw [← journalStream.toLawful_canonical _ _ journal,
            ← encodeDeltas_decodeDeltas deltas] at outer
          simp only [Log.encode, Log.deltas, List.reverse_reverse, List.append_assoc, outer]
          conv => rhs; rw [← List.take_append_drop logMagic.length bytes]
          rw [exact]

/-- A restored log re-encodes to exactly the physical image it was read from. -/
theorem restoreLog_encode_eq {expected : Context} {bytes : Bytes} {l : Log} {s : Replica}
    (h : restoreLog expected bytes = some (l,s)) : l.encode = bytes := by
  unfold restoreLog at h
  cases decoded : decodeLog bytes with
  | none => simp [decoded] at h
  | some l' =>
    cases replayed : replayLog expected l' with
    | none => simp [decoded, replayed] at h
    | some s' =>
      simp [decoded, replayed] at h
      rw [← h.1]
      exact decodeLog_canonical decoded

theorem Log.merged_push (l : Log) (d : Delta) :
    (l.push d).merged =
      { l.merged with
        events := l.merged.events ++ d.events
        commitWitnesses := l.merged.commitWitnesses ++ d.witnesses } := by
  simp [Log.merged, Log.push, Log.deltas, List.append_assoc]

theorem Log.encode_push (l : Log) (d : Delta) :
    (l.push d).encode = l.encode ++ deltaFrame d := by
  simp [Log.encode, Log.push, Log.deltas, encodeDeltas_append, List.append_assoc]

theorem restoreLog_encode (context : Context) (l : Log) :
    restoreLog context l.encode = (replayLog context l).map (fun s => (l,s)) := by
  unfold restoreLog
  rw [decodeLog_encode]
  cases h : replayLog context l <;> simp [h]

theorem replayLog_of_restoreLog {context : Context} {l : Log} {state : Replica}
    (h : restoreLog context l.encode = some (l,state)) : replayLog context l = some state := by
  rw [restoreLog_encode] at h
  cases r : replayLog context l with
  | none => simp [r] at h
  | some s => simp [r] at h; simp [h]

/-- The fast append is exactly the original whole-log replay of the extended
image: replay of the old log, then only the appended entries. -/
theorem replayLog_push (context : Context) (l : Log) (state next : Replica) (d : Delta)
    (old : replayLog context l = some state)
    (continued : replayEvents context.config (chainDigest context) state d.events = some next)
    (notFailed : next.core.failed = false) :
    replayLog context (l.push d) = some next := by
  unfold replayLog at old ⊢
  rw [Log.merged_push]
  dsimp only
  by_cases guard : (l.merged.context != context || !context.wellFormed ||
      decide (l.merged.self ≥ context.config.parties) ||
      !(l.merged.snapshot.map fun n => n.core.self == l.merged.self && !n.core.failed).getD true) = true
  · simp [guard] at old
  · simp only [guard, Bool.false_eq_true, ↓reduceIte] at old ⊢
    cases replayed : replayEvents context.config (chainDigest context)
        (l.merged.snapshot.getD (Replica.start context.config (chainDigest context) l.merged.self l.merged.initialTime))
        l.merged.events with
    | none => simp [replayed] at old
    | some s =>
      rw [replayed] at old
      simp at old
      obtain ⟨_, rfl⟩ := old
      rw [replay_append, replayed]
      simp [continued, notFailed]

theorem restoreLog_push (context : Context) (l : Log) (state next : Replica) (d : Delta)
    (old : restoreLog context l.encode = some (l,state))
    (continued : replayEvents context.config (chainDigest context) state d.events = some next)
    (notFailed : next.core.failed = false) :
    restoreLog context (l.push d).encode = some (l.push d,next) := by
  rw [restoreLog_encode, replayLog_push context l state next d
    (replayLog_of_restoreLog old) continued notFailed]
  rfl

/-! ## Checkpoints

A checkpoint replaces a log by one base frame whose snapshot is the log's replayed replica,
with no events and no deltas, carrying the COMMIT witnesses the replica can still use
(`retains`). Reopening it decodes the replica instead of replaying the history, and its size
is bounded by the replica's live state. The replaced image is kept by the writer as the
previous segment (`*.log.upto-N`), so the whole input history stays auditable as a chain of
segments. -/

/-- A kept signature the replica can still use: for a view above its floor (a COMMIT not
yet counted, or held), or for a commit whose evidence it still serves. -/
def retains (r : Replica) (w : CommitWitness) : Bool :=
  r.core.lastCommitted < w.view ||
    r.evidence.any fun entry => entry.2.2.any fun m => m.view == w.view && m.sender == w.attestation.signer

/-- The base journal of a checkpoint. -/
def Log.checkpointBase (l : Log) (s : Replica) : Journal :=
  { l.merged with
    events := []
    snapshot := some s
    commitWitnesses := l.merged.commitWitnesses.filter (retains s) }

def Log.checkpoint (l : Log) (s : Replica) : Log := ⟨l.checkpointBase s, []⟩

theorem Log.checkpoint_merged (l : Log) (s : Replica) :
    (l.checkpoint s).merged = l.checkpointBase s := by
  simp [Log.checkpoint, Log.checkpointBase, Log.merged, Log.deltas]

/-- A checkpoint of a log replays to the same replica. -/
theorem replayLog_checkpoint {context : Context} {l : Log} {s : Replica}
    (h : replayLog context l = some s) : replayLog context (l.checkpoint s) = some s := by
  have kept := replayLog_kept h
  unfold replayLog at h ⊢
  dsimp only at h ⊢
  split at h
  · simp at h
  · rename_i guardFalse
    cases replayed : replayEvents context.config (chainDigest context)
        (l.merged.snapshot.getD (Replica.start context.config (chainDigest context) l.merged.self l.merged.initialTime))
        l.merged.events with
    | none => simp [replayed] at h
    | some t =>
      rw [replayed] at h
      change (if t.core.failed = true then none else pure t) = some s at h
      split at h
      · simp at h
      · rename_i passed
        have ts : t = s := by simpa [pure] using h
        subst ts
        rw [Log.checkpoint_merged]
        simp_all [replayEvents, Log.checkpointBase]

theorem restoreLog_checkpoint (context : Context) (l : Log) (s : Replica)
    (h : restoreLog context l.encode = some (l,s)) :
    restoreLog context (l.checkpoint s).encode = some (l.checkpoint s,s) := by
  rw [restoreLog_encode, replayLog_checkpoint (replayLog_of_restoreLog h)]
  rfl

#assert_axioms replayLog_checkpoint
#assert_axioms restoreLog_checkpoint

/-- In-process authoritative image of this replica's journal. `length` is the
exact physical byte length the single writer compares before appending. `chain` is the
domain's digest, built once (its origin hashes the whole context). `deltas` counts the delta
frames since the last checkpoint, kept by the append: no caller walks `log.recent`. -/
structure Restored (context : Context) where
  log : Log
  state : Replica
  length : Nat
  witnesses : List CommitWitness
  chain : ChainDigest
  deltas : Nat
  exact : restoreLog context log.encode = some (log,state)
  sized : log.encode.length = length
  witnessed : witnesses = log.merged.commitWitnesses
  chained : chain = chainDigest context
  counted : deltas = log.recent.length

def Restored.self {context : Context} (r : Restored context) : Nat := r.log.base.self

/-- Reopen a physical image. `restoreLog` already compared the re-encoding with
the image (`restoreLog_encode_eq`); no second encode or comparison runs here. -/
def openRestored (context : Context) (bytes : Bytes) : Option (Restored context) :=
  match h : restoreLog context bytes with
  | none => none
  | some (l,s) =>
    have same : l.encode = bytes := restoreLog_encode_eq h
    some ⟨l,s,bytes.length,l.merged.commitWitnesses,chainDigest context,l.recent.length,
      same ▸ h,by rw [same],rfl,rfl,rfl⟩

theorem Log.merged_self (l : Log) : l.merged.self = l.base.self := rfl

/-- Execute only the appended entries; the result carries the whole-replay
equation for the extended physical image. Returns the exact frame to append. -/
def appendRestored {context : Context} (old : Restored context)
    (events : List Event) (witnesses : List CommitWitness) : Option (Restored context × Bytes) :=
  match continued : replayEvents context.config old.chain old.state events with
  | none => none
  | some next =>
    -- Nothing is checked here: the replayed replica has not failed and is still this
    -- journal's (`replayEvents_kept` from `replayLog_kept` of the image it extends).
    let d : Delta := ⟨events,witnesses⟩
    some (⟨old.log.push d,next,old.length + (deltaFrame d).length,
      old.witnesses ++ witnesses,old.chain,old.deltas + 1,
      restoreLog_push context old.log old.state next d old.exact (old.chained ▸ continued)
        ((replayEvents_kept context.config old.chain events old.state next continued).2
          (replayLog_kept (replayLog_of_restoreLog old.exact)).2),
      by rw [Log.encode_push, List.length_append, old.sized],
      by rw [Log.merged_push, old.witnessed],old.chained,
      by rw [old.counted]; rfl⟩,deltaFrame d)

theorem appendRestored_exact {context : Context} (next : Restored context) :
    restoreLog context next.log.encode = some (next.log,next.state) := next.exact

#assert_axioms decodeLog_encode
#assert_axioms restoreLog_push
#assert_axioms replayEvents_kept
#assert_axioms replayLog_kept
#assert_axioms restoreLog_encode_eq
#assert_axioms decodeLog_canonical
#assert_axioms encodeDeltas_eq_encodeDeltasTR
#assert_axioms decodeDeltas_eq_decodeDeltasTR
#assert_axioms appendRestored_exact

/-- A base-255 length prefix (`StreamCodec.nat`'s digits then byte 255): its
value, the number of bytes it occupies, and the remainder. One loop step per
digit. -/
def natPrefixCounted (bytes : Bytes) : Option (Nat × Nat × Bytes) :=
  go bytes 0 1 0
where
  go : Bytes → Nat → Nat → Nat → Option (Nat × Nat × Bytes)
  | [], _, _, _ => none
  | byte :: rest, value, scale, digits =>
    if byte = 255 then some (value, digits + 1, rest)
    else go rest (value + byte.toNat * scale) (scale * 255) (digits + 1)

/-- Classify the delta frames after the base frame. `valid` is the byte length
of the complete frames so far; it grows by each frame's size, never by
re-measuring the remainder. -/
def scanFrames : Nat → Bytes → Nat → Option Nat
  | 0, rest, valid => if rest.isEmpty then some valid else none
  | fuel + 1, rest, valid =>
    if rest.isEmpty then some valid else
    match natPrefixCounted rest with
    | none =>
      -- Torn: the length digits never terminate. A 255 inside them is corruption.
      if rest.contains 255 then none else some valid
    | some (count,digits,afterCount) =>
      let (payload,next) := afterCount.splitAt count
      -- Torn: fewer payload bytes than declared.
      if payload.length < count then some valid
      else if (deltaStream.toLawful.decode payload).isNone then none
      else scanFrames fuel next (valid + digits + count)

/-- A reader's classification of a physical image: the longest prefix of
complete frames, and whether the remainder is an unacknowledged torn frame.
A complete but undecodable frame is corruption and is never truncated. Linear
in the image: each frame is visited once. -/
def scanLog (bytes : Bytes) : Option Nat :=
  if bytes.take logMagic.length != logMagic then none else
  match bytesStream.decodePrefix (bytes.drop logMagic.length) with
  | none => none
  | some (_,afterBase) =>
    let total := bytes.length
    let rest := afterBase.length
    scanFrames (rest + 1) afterBase (total - rest)


structure Crypto where
  /-- Concrete ML-DSA-65 implementation, context MiniJointAgreementV1. -/
  verify : Bytes → Bytes → Bytes → IO Bool
  sign : Bytes → IO Bytes
def verifyAttestations (crypto : Crypto) (expected : Context) (bytes : Bytes)
    (signers : List Attestation) : IO Bool := do
  if !expected.wellFormed || signers.length < expected.config.quorum ||
      (signers.map Attestation.signer).eraseDups.length != signers.length then
    return false
  for a in signers do
    if a.signer ≥ expected.config.parties || a.signature.length != 3309 then return false
    let some pk := expected.publicKeys[a.signer]? | return false
    if !(← crypto.verify pk bytes a.signature) then return false
  return true
/-- A certificate is checked against its statement alone: the cost is the signatures, and
does not depend on the chain. -/
def verifyCertificate (crypto : Crypto) (expected : Context) (cert : Certificate) : IO Bool := do
  if cert.context != expected || cert.view == 0 || cert.length == 0 then return false
  verifyAttestations crypto expected
    (commitStatementBytes expected cert.view cert.length cert.digest) cert.signers

/-- A checked network commitment, never deserialized directly. Its constructor
is private to this module, whose sole public producer pins the expected Context
and verifies a quorum of real signatures. This is an IO verification boundary,
not a proof of ML-DSA unforgeability or the whole distributed algorithm. It names a chain
by its length and digest and carries none of it. -/
structure VerifiedCommit (expected : Context) where
  private mk ::
  private certificate : Certificate
  private pinned : certificate.context = expected
  private quorum : expected.config.quorum ≤ certificate.signers.length
  private distinct : (certificate.signers.map Attestation.signer).Nodup
  private members : ∀ a ∈ certificate.signers, a.signer < expected.config.parties
def VerifiedCommit.context {expected : Context} (_v : VerifiedCommit expected) : Context := expected
def VerifiedCommit.view {expected : Context} (v : VerifiedCommit expected) : Nat := v.certificate.view
def VerifiedCommit.length {expected : Context} (v : VerifiedCommit expected) : Nat := v.certificate.length
def VerifiedCommit.digest {expected : Context} (v : VerifiedCommit expected) : Bytes := v.certificate.digest
def VerifiedCommit.bytes {expected : Context} (v : VerifiedCommit expected) : Bytes := certificateStream.encode v.certificate
def VerifiedCommit.signerIds {expected : Context} (v : VerifiedCommit expected) : List Nat :=
  v.certificate.signers.map Attestation.signer
/-- `history` is the application history of the chain the commit is for, as far as the
signed digest says: its running digest is the application half of the statement
(`chainDigest_history` is why a correct signer's chain has that history). A reader that
holds the source records checks this with no part of the chain; that two histories with one
digest are equal is the digest's collision-freedom, an assumption wherever it is used. -/
def VerifiedCommit.Reads {expected : Context} (v : VerifiedCommit expected) (history : Block) : Prop :=
  (historyDigest expected).of history = historyHalf v.digest
instance {expected : Context} (v : VerifiedCommit expected) (history : Block) : Decidable (v.Reads history) :=
  inferInstanceAs (Decidable ((historyDigest expected).of history = historyHalf v.digest))
theorem VerifiedCommit.signers_distinct {expected : Context} (v : VerifiedCommit expected) :
    v.signerIds.Nodup := v.distinct
theorem VerifiedCommit.quorum_size {expected : Context} (v : VerifiedCommit expected) :
    expected.config.quorum ≤ v.signerIds.length := by
  simpa [VerifiedCommit.signerIds] using v.quorum
theorem VerifiedCommit.signers_members {expected : Context} (v : VerifiedCommit expected)
    (id : Nat) (member : id ∈ v.signerIds) : id < expected.config.parties := by
  obtain ⟨a,inside,same⟩ := List.mem_map.mp member
  rw [← same]
  exact v.members a inside
def verifyCommitted (crypto : Crypto) (expected : Context)
    (certificate : Certificate) : IO (Option (VerifiedCommit expected)) := do
  if pinned : certificate.context = expected then
    if quorum : expected.config.quorum ≤ certificate.signers.length then
      if distinct : (certificate.signers.map Attestation.signer).Nodup then
        if members : ∀ a ∈ certificate.signers, a.signer < expected.config.parties then
          if ← verifyCertificate crypto expected certificate then
            return some (VerifiedCommit.mk certificate pinned quorum distinct members)
          else return none
        else return none
      else return none
    else return none
  else return none

/-- The signature is checked against the statement before any block is read; the kernel's
`decode` then checks the block a delivery carries against the same statement. -/
def verifyCommitWitness (crypto : Crypto) (expected : Context)
    (witness : CommitWitness) : IO Bool := do
  if !expected.wellFormed || witness.view == 0 || witness.length == 0 ||
      witness.attestation.signer ≥ expected.config.parties ||
      witness.attestation.signature.length != 3309 then return false
  let some pk := expected.publicKeys[witness.attestation.signer]? | return false
  crypto.verify pk (commitStatementBytes expected witness.view witness.length witness.digest)
    witness.attestation.signature

inductive Result where
  | invalid | conflict | uncertain
  | durable (state : Replica)
  deriving Repr

inductive PersistResult where
  | conflict | uncertain | durable
  deriving DecidableEq, BEq, Repr

/-- The replica's journal as seen by its single writer process. `current` is
the authoritative in-memory image; `append` is the helper's length-checked
append. A read-only storage has no writer and refuses appends. -/
structure Storage where
  current : IO (Option (Sigma Restored))
  install : Option (Sigma Restored) → IO Unit
  append : Nat → ByteArray → IO PersistResult
  /-- Atomically replace the whole image if its length is still the given one
  (a checkpoint); the writer keeps the replaced image as the previous segment. -/
  replace : Nat → ByteArray → IO PersistResult
  deriving Inhabited

def current (storage : Storage) (context : Context) : IO (Option (Restored context)) := do
  let some prior ← storage.current | return none
  if same : prior.1 = context then return some (same ▸ prior.2) else return none

def Storage.readOnly (snapshot : Sigma Restored) : Storage where
  current := return some snapshot
  install _ := throw (IO.userError "read-only agreement journal")
  append _ _ := return .conflict
  replace _ _ := return .conflict

/-- A new image is installed only after the exact frame was durably appended at
the expected length. Conflict or uncertainty drops the image: the owner must
reopen from disk; nothing proceeds on a guessed state. -/
def commitRestored {context : Context} (storage : Storage) (prior next : Restored context)
    (frame : Bytes) : IO Result := do
  match ← storage.append prior.length frame.toByteArray with
  | .conflict => storage.install none; return .conflict
  | .uncertain => storage.install none; return .uncertain
  | .durable =>
    storage.install (some ⟨context,next⟩)
    return .durable next.state

/-- The checkpoint of a restored image: the same replica from one base frame, with the
witnesses it can still use. Its replay equation is `restoreLog_checkpoint`;
nothing is replayed to build it. -/
def checkpointRestored {context : Context} (prior : Restored context) : Restored context × Bytes :=
  let l := prior.log.checkpoint prior.state
  (⟨l,prior.state,l.encode.length,prior.witnesses.filter (retains prior.state),prior.chain,0,
    restoreLog_checkpoint context prior.log prior.state prior.exact,rfl,
    by rw [Log.checkpoint_merged, prior.witnessed]; rfl,prior.chained,rfl⟩,l.encode)

/-- Deltas after which a standing replica checkpoints its journal, bounding the
replay a reopen performs. -/
def checkpointEvery : Nat := 1024

/-- Replace the durable image by its checkpoint. Conflict or uncertainty drops
the in-memory image, exactly as for an append: the owner reopens from disk. -/
def checkpoint (storage : Storage) (context : Context) : IO PersistResult := do
  let some prior ← current storage context | return .conflict
  let (next,bytes) := checkpointRestored prior
  match ← storage.replace prior.length bytes.toByteArray with
  | .durable => storage.install (some ⟨context,next⟩); return .durable
  | .conflict => storage.install none; return .conflict
  | .uncertain => storage.install none; return .uncertain

/-- Audit of a replica's whole retained input history: its checkpoint segments
in order, then the live image. The first must be a genesis journal (no
snapshot), replayed from `Replica.start`; every later one must open with exactly the
replica the previous one replays to. Returns the final replayed replica. -/
def auditSegments (context : Context) (images : List Bytes) : Except String Replica := do
  let mut origin : Option Replica := none
  let mut index := 0
  for bytes in images do
    let some valid := scanLog bytes | throw s!"segment {index}: not a journal image"
    if valid != bytes.length then throw s!"segment {index}: torn tail inside the retained history"
    let some (l,s) := restoreLog context bytes | throw s!"segment {index}: does not replay under this context"
    match origin with
    | none => if l.base.snapshot.isSome then throw s!"segment {index}: the history does not begin at genesis"
    | some previous =>
      if l.base.snapshot != some previous then
        throw s!"segment {index}: its snapshot is not the state the previous segment replays to"
    origin := some s
    index := index + 1
  match origin with
  | none => throw "no journal segments"
  | some s => return s

/-- A delivery the replica's state already accounts for: journaling it again would change
nothing a later input reads. A message it has received, a proposal for a view that has one,
a message for a view at or below its floor, a block it cannot read from a sender that is not
ahead, a COMMIT it already holds. Skipping a delivery is a schedule the network may always
choose, so this needs no argument about `step`.

CANDIDATE(⊥) is never settled. A member repeats it while it is stuck in a view, once per
timeout, and each repeat is what the kernel answers with the evidence or the messages the
member is owed (`serveFloor`, `serveViews`, `deliver`): swallowing it as a duplicate would
leave a stranded member stranded. -/
def settled (h : ChainDigest) (r : Replica) (w : WireMessage) : Bool :=
  if w.kind == .candidate && w.value.isNone then false else
  match decode h r w with
  | some m =>
      m.view ≤ r.core.lastCommitted || (viewAt r.core m.view).received.contains m ||
        (m.kind == .propose && (viewAt r.core m.view).proposal.isSome)
  | none => r.far.contains w || w.height ≤ r.height

theorem candidate_bottom_never_settled (h : ChainDigest) (r : Replica) (w : WireMessage)
    (candidate : w.kind = .candidate) (bottom : w.value = none) : settled h r w = false := by
  simp [settled, candidate, bottom]

#assert_axioms candidate_bottom_never_settled

def CommitWitness.same (a b : CommitWitness) : Bool :=
  a.view == b.view && a.length == b.length && a.digest == b.digest &&
    a.attestation.signer == b.attestation.signer

/-- Authenticated peer delivery. A settled message leaves the durable image unchanged and
writes nothing. A COMMIT's verified signature is retained in the same append as its counted
delivery: a crash cannot keep one without the other. -/
def receiveDelivery (storage : Storage) (context : Context)
    (time : Nat) (message : WireMessage) (witness : Option CommitWitness) : IO Result := do
  let some prior ← current storage context | return .invalid
  if settled prior.chain prior.state message then return .durable prior.state
  let added := witness.toList.filter fun w => !prior.witnesses.any (CommitWitness.same w)
  let some (next,frame) := appendRestored prior [encodeEntry (.input (.deliveryAt time message))] added
    | return .invalid
  commitRestored storage prior next frame

/-- Append one exact entry using the proved continuation of the prior replay. -/
def persist (storage : Storage) (context : Context) (entry : Entry) : IO Result := do
  let some prior ← current storage context | return .invalid
  let some (next,frame) := appendRestored prior [encodeEntry entry] [] | return .invalid
  commitRestored storage prior next frame

/-- Candidate dissemination persists only unvalidated offers. Every complete
source record remains subject to the native historical checker before checked.
`records` are source records from application height `height`; every one above this
replica's committed records that it neither offers nor has committed is kept, so
restart and catch-up rediscover the work. -/
def retainCandidateOffers (storage : Storage) (context : Context) (height : Nat) (records : Block) :
    IO Result := do
  let some prior ← current storage context | return .invalid
  let run := (above height prior.state.records records).getD []
  let fresh := run.filter (fun payload => !payload.isEmpty &&
    !prior.state.core.offers.contains payload && !prior.state.committed.contains payload)
  if fresh.isEmpty then return .durable prior.state
  let some (next,frame) := appendRestored prior
      (fresh.map (fun payload => encodeEntry (.input (.offer payload)))) [] | return .invalid
  commitRestored storage prior next frame

/-- Verification, protocol delivery and retained transferable evidence share one
journal append. Only this producer accepts peer signatures. The COMMIT may have been
written by its signer or passed on by any member: the signature is the signer's, over the
statement the message carries. -/
def receiveCommit (storage : Storage) (crypto : Crypto) (context : Context)
    (time : Nat) (message : WireMessage) (signature : Bytes) : IO Result := do
  let some (length,digest) := message.statement | return .invalid
  if message.kind != .commit then return .invalid
  let witness : CommitWitness := ⟨message.view,length,digest,⟨message.sender,signature⟩⟩
  -- A COMMIT the replica already accounts for was verified when it was first taken.
  let some prior ← current storage context | return .invalid
  if settled prior.chain prior.state message then return .durable prior.state
  if !(← verifyCommitWitness crypto context witness) then return .invalid
  receiveDelivery storage context time message (some witness)

/-- The COMMITs of the commits a replica keeps evidence for, from committed height `height`
on, in order, as a member at that height reads them: exactly what the kernel owes a member
that asks to leave a view from that height (`GenericSimplexRelative.deliver`). Empty unless
`height` is below the replica's own and is the origin of a kept commit. -/
def keptCommits (h : ChainDigest) (r : Replica) (height : Nat) : List WireMessage :=
  if height < r.height && r.evidence.any (fun entry => entry.1 == height) then
    (r.evidence.filter fun entry => height ≤ entry.1).flatMap fun entry =>
      entry.2.2.map (encode h entry.1 entry.2.1)
  else []

/-- The durable send cause of a COMMIT this replica signs: the message is in its own
undrained output, as a broadcast or as evidence it owes a peer, or it is one of the COMMITs
of a commit it keeps evidence for (its own COMMIT that committed that block, which it sent
when it was made). Each is written by an acknowledged journal entry before anything is
signed, and signing the same statement again says nothing new. -/
def ownCommit {context : Context} (prior : Restored context) (message : WireMessage) : Bool :=
  message.kind == .commit && message.sender == prior.self && message.statement.isSome &&
    (prior.state.sends.contains message || (prior.state.owed.any fun entry => entry.2 == message) ||
      prior.state.evidence.any fun entry =>
        entry.2.2.any fun m => encode prior.chain entry.1 entry.2.1 m == message)

/-- The transferable signature a COMMIT leaves with: this replica's own, made now for a
COMMIT in its durable output, or the signer's, kept since it was received. A COMMIT with
neither is not sent. -/
def commitProof (storage : Storage) (crypto : Crypto) (context : Context)
    (message : WireMessage) : IO (Option Bytes) := do
  let some prior ← current storage context | return none
  let some (length,digest) := message.statement | return none
  if message.sender == prior.self then
    if !ownCommit prior message then return none
    let signature ← crypto.sign (commitStatementBytes context message.view length digest)
    if signature.length != 3309 then return none
    return some signature
  else
    return (prior.witnesses.find? fun w => w.signs message).map (·.attestation.signature)

/-- The certificate of the newest commit this replica keeps evidence for: the signatures
kept with the COMMITs that committed it, and its own if it sent one. Any replica that
committed can produce it; the result is reverified, not cast. The statement is read off
the evidence: every message of an entry is for one block, written from the entry's height. -/
def recoverCommitment (storage : Storage) (crypto : Crypto) (context : Context) :
    IO (Option (VerifiedCommit context)) := do
  let some prior ← current storage context | return none
  let some (height,digest,messages) := prior.state.evidence.getLast? | return none
  let some first := messages.head? | return none
  let some run := first.value | return none
  let length := height + run.length
  let stated := prior.chain.over digest run
  let mut signers : List Attestation := []
  for m in messages do
    if m.kind == .commit && m.value == some run && !signers.any (fun a => a.signer == m.sender) then
      if m.sender == prior.self then
        let signature ← crypto.sign (commitStatementBytes context first.view length stated)
        if signature.length == 3309 then signers := signers ++ [⟨m.sender,signature⟩]
      else if let some w := prior.witnesses.find? (fun w => w.view == first.view && w.length == length &&
          w.digest == stated && w.attestation.signer == m.sender) then
        signers := signers ++ [w.attestation]
  verifyCommitted crypto context ⟨context,first.view,length,stated,signers⟩
end Minidregg.Compiler.GenericSimplexIO
