/-
# Compiler.DurableReceiverIO — real internal receiving loop

Lean decodes and replays the image, calls the existing durable executor, and
selects the ONLY candidate bytes supplied to the native exact-byte CAS. The
native process never interprets an intent. Every reported committed result is
confirmed by reopening and finding the exact journaled intent. An ambiguous
native response is uncertainty until this readback succeeds.

This module exposes no untrusted wire-request admission endpoint. Its caller
must supply the `DataIntent` constructed by the accepted controller. The
physical assumptions are SQLite transaction integrity, honest byte transport,
and the filesystem/OS durability floor; no Lean theorem proves those systems.
-/
import Compiler.DurableReceiverCodec

namespace Minidregg.Compiler.DurableReceiverIO

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Compiler.DurableReceiverCodec

set_option autoImplicit false

inductive CasObservation where
  | installed
  | alreadyPresent
  | conflict
  | uncertain (detail : String)
  deriving Repr, DecidableEq

/-- The only native boundary: opaque exact bytes and explicit observations.
An error is not proof that a transaction failed before commit. -/
structure Transport where
  read : IO (Except String (Option (List UInt8)))
  cas : Option (List UInt8) → List UInt8 → IO CasObservation

structure NativeConfig where
  binary : System.FilePath
  root : System.FilePath

def runNative (config : NativeConfig) (arguments : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := config.binary.toString, args := arguments }

def parseCasOutput (output : IO.Process.Output) : CasObservation :=
  if output.exitCode == 0 && output.stderr == "" then
    match output.stdout with
    | "Installed\n" => .installed
    | "AlreadyPresent\n" => .alreadyPresent
    | _ => .uncertain "malformed native success response"
  else if output.exitCode == 4 && output.stdout == "" then
    .conflict
  else
    .uncertain s!"native CAS response lost or failed (exit {output.exitCode}): {output.stderr}"

def NativeConfig.read (config : NativeConfig) : IO (Except String (Option (List UInt8))) :=
  try
    IO.FS.withTempDir fun directory => do
      let path := directory / "snapshot.bin"
      let output ← runNative config #["read-to", config.root.toString, path.toString]
      if output.exitCode == 0 && output.stdout == "" && output.stderr == "" then
        return .ok (some (← IO.FS.readBinFile path).toList)
      else if output.exitCode == 3 && output.stdout == "" then
        return .ok none
      else
        return .error s!"native read failed or malformed (exit {output.exitCode}): {output.stderr}"
  catch error => pure (.error s!"native read unavailable: {error}")

/-- `crashAt` is a lifecycle-test hook implemented by process exit in the
shared native CAS. Production `transport` always supplies `none`. -/
def NativeConfig.cas (config : NativeConfig) (expected : Option (List UInt8))
    (proposed : List UInt8) (crashAt : Option String := none) : IO CasObservation :=
  try
    IO.FS.withTempDir fun directory => do
      let postPath := directory / "post.bin"
      IO.FS.writeBinFile postPath proposed.toByteArray
      let expectedArgument ← match expected with
        | none => pure "-"
        | some bytes => do
            let path := directory / "pre.bin"
            IO.FS.writeBinFile path bytes.toByteArray
            pure path.toString
      let arguments := match crashAt with
        | none => #["cas", config.root.toString, expectedArgument, postPath.toString]
        | some phase => #["cas-crash", config.root.toString, expectedArgument, postPath.toString, phase]
      let output ← runNative config arguments
      return parseCasOutput output
  catch error => pure (.uncertain s!"native CAS unavailable: {error}")

def NativeConfig.transport (config : NativeConfig) : Transport :=
  ⟨config.read, fun expected proposed => config.cas expected proposed⟩

structure Loaded (rootBytes : List UInt8 → Digest) where
  bytes : List UInt8
  image : Image
  snapshot : DataSnapshot rootBytes
  canonical : encode image = bytes
  represented : image.restore rootBytes = some snapshot

/-- Reuse the already restored snapshot when a controller reconstructs its
typed directory; this performs no second journal replay or cell update. -/
def Loaded.cells {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    List (CellId × List UInt8) :=
  loaded.image.cellIds.map fun cellId => (cellId, loaded.snapshot.canonicalBytes cellId)

theorem Loaded.cells_exact {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    loaded.image.currentCells rootBytes = some loaded.cells := by
  simp [Image.currentCells, loaded.represented, Loaded.cells]

def loadBytes (rootBytes : List UInt8 → Digest) (bytes : List UInt8) :
    Except String (Loaded rootBytes) :=
  match decoded : decode bytes with
  | none => .error "noncanonical or unsupported durable image"
  | some image =>
      match restored : image.restore rootBytes with
      | none => .error "durable image journal does not replay through the canonical executor"
      | some snapshot => .ok ⟨bytes, image, snapshot, decode_canonical decoded, restored⟩

def load (transport : Transport) (rootBytes : List UInt8 → Digest) :
    IO (Except String (Loaded rootBytes)) := do
  match ← transport.read with
  | .error message => return .error message
  | .ok none => return .error "durable image is not initialized"
  | .ok (some bytes) => return loadBytes rootBytes bytes

inductive Confirmation where
  | installed
  | recoveredAfterUncertainResponse
  | replayed
  deriving Repr, DecidableEq

inductive Result (rootBytes : List UInt8 → Digest) where
  /-- Exact physical readback confirmed this snapshot's journal contains the
  intent. A concurrent later turn may instead require full reopened replay. -/
  | confirmed (kind : Confirmation) (snapshot : DataSnapshot rootBytes)
  | rejected (reason : RejectReason)
  | contention
  | unavailable (detail : String)
  /-- A CAS was attempted; durable success could not be established. -/
  | uncertain (detail : String)

def confirm (transport : Transport) (rootBytes : List UInt8 → Digest)
    (intent : DataIntent rootBytes) (kind : Confirmation) : IO (Result rootBytes) := do
  match ← load transport rootBytes with
  | .error message => return .uncertain s!"CAS attempted; readback unavailable: {message}"
  | .ok loaded =>
      match DurableDataIntent.execute .complete loaded.snapshot intent with
      | .replayed _ => return .confirmed kind loaded.snapshot
      | _ => return .uncertain "CAS attempted; reopened journal does not confirm the exact intent"

/-- An exact readback of the only prepared CAS candidate denotes its already
checked next snapshot. The candidate is tied to the original loaded image and
accepted intent by `Ready.restored`, rather than a digest or caller-supplied
summary. -/
theorem prepared_exact_readback {rootBytes : List UInt8 → Digest}
    {image : Image} {before : DataSnapshot rootBytes} {intent : DataIntent rootBytes}
    (ready : Ready rootBytes image before intent) (readback : List UInt8)
    (exact : readback = encode (image.append intent)) :
    ∃ loaded : Loaded rootBytes, loaded.bytes = readback ∧ loaded.snapshot = ready.next := by
  subst readback
  exact ⟨⟨encode (image.append intent), image.append intent, ready.next, rfl,
    ready.restored⟩, rfl, rfl⟩

/-- ByteArray's derived equality compares every byte, with no digest premise.
This bridge lets the stack-safe native comparison discharge exact list-byte
identity before using the prepared snapshot. -/
theorem byteArray_beq_exact (left right : List UInt8) :
    (left.toByteArray == right.toByteArray) = true ↔ left = right := by
  have byteArrayBEq (a b : ByteArray) : (a == b) = true ↔ a = b := by
    cases a with
    | mk data =>
      cases b with
      | mk other =>
        unfold BEq.beq ByteArray.instBEq
        unfold ByteArray.instBEq.beq
        simp only [ByteArray.mk.injEq, beq_iff_eq]
  rw [byteArrayBEq]
  constructor
  · intro exact
    have lists := congrArg (fun bytes : ByteArray => bytes.data.toList) exact
    simpa using lists
  · intro exact
    subst right
    rfl

/-- Read once after CAS. Equal complete bytes reuse the prepared executor's
proved next snapshot; changed bytes follow the existing canonical reopen and
replay check, which admits a concurrent later commit without hiding it. -/
private def confirmPrepared (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) (intent : DataIntent rootBytes)
    (ready : Ready rootBytes loaded.image loaded.snapshot intent)
    (proposed : List UInt8) (_canonical : proposed = encode (loaded.image.append intent))
    (kind : Confirmation) : IO (Result rootBytes) := do
  match ← transport.read with
  | .error message => return .uncertain s!"CAS attempted; readback unavailable: {message}"
  | .ok none => return .uncertain "CAS attempted; readback unavailable: durable image is not initialized"
  | .ok (some readback) =>
      if exact : readback.toByteArray == proposed.toByteArray then
        have exactBytes : readback = proposed := (byteArray_beq_exact readback proposed).mp exact
        have _ : ∃ reread : Loaded rootBytes,
            reread.bytes = readback ∧ reread.snapshot = ready.next :=
          prepared_exact_readback ready readback (exactBytes.trans _canonical)
        return .confirmed kind ready.next
      match loadBytes rootBytes readback with
      | .error message => return .uncertain s!"CAS attempted; readback unavailable: {message}"
      | .ok reopened =>
          match DurableDataIntent.execute .complete reopened.snapshot intent with
          | .replayed _ => return .confirmed kind reopened.snapshot
          | _ => return .uncertain "CAS attempted; reopened journal does not confirm the exact intent"

/-- Publish against the exact image on which the controller admitted the
operation. In particular, a logical height derived from `loaded.image` cannot
silently acquire a later journal boundary between admission and publication.

There is one CAS attempt and no rebase. A caller wishing to retry contention
must reconstruct admission from a fresh image. Physical success still requires
the existing exact-intent readback; a lost response never becomes a refusal. -/
def receiveLoaded (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) (intent : DataIntent rootBytes) :
    IO (Result rootBytes) := do
  match prepare loaded.image loaded.snapshot loaded.represented intent with
  | .inr (.replayed _) => return .confirmed .replayed loaded.snapshot
  | .inr (.rejected reason) => return .rejected reason
  | .inr _ => return .unavailable "unexpected complete-schedule outcome"
  | .inl ready =>
      let proposed := encode (loaded.image.append intent)
      match ← transport.cas (some loaded.bytes) proposed with
      | .installed | .alreadyPresent =>
          confirmPrepared transport rootBytes loaded intent ready proposed rfl .installed
      | .conflict => return .contention
      | .uncertain _ =>
          confirmPrepared transport rootBytes loaded intent ready proposed rfl
            .recoveredAfterUncertainResponse

/-- Bounded contention retry for an already constructed internal intent whose
admission does not depend on a journal-wide clock. Controllers deriving authority
or time from one loaded image must instead call `receiveLoaded` with that image.
Each retry here reloads and repeats the canonical durable guard checks. -/
def receive (transport : Transport) (rootBytes : List UInt8 → Digest)
    (intent : DataIntent rootBytes) : Nat → IO (Result rootBytes)
  | 0 => pure .contention
  | attempts + 1 => do
      match ← load transport rootBytes with
      | .error message => return .unavailable message
      | .ok loaded =>
          match ← receiveLoaded transport rootBytes loaded intent with
          | .contention => receive transport rootBytes intent attempts
          | result => return result

/-- Explicit bootstrap, separate from receipt acceptance. Existing different
images are never replaced; initialization is confirmed by exact byte readback. -/
def bootstrap (transport : Transport) (rootBytes : List UInt8 → Digest)
    (seed : Seed) : IO (Except String Unit) := do
  let image : Image := ⟨seed, []⟩
  if (image.restore rootBytes).isNone then
    return .error "invalid bootstrap seed"
  let bytes := encode image
  let observation ← transport.cas none bytes
  match ← transport.read with
  | .ok (some current) =>
      if current == bytes then return .ok ()
      else return .error s!"bootstrap did not install exact seed: {repr observation}"
  | .ok none => return .error s!"bootstrap absent after CAS: {repr observation}"
  | .error message => return .error s!"bootstrap outcome uncertain: {message}"

end Minidregg.Compiler.DurableReceiverIO
