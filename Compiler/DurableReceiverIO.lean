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
  /-- `snapshot` was reread from the physical store and its journal contains
  this exact intent. It may include concurrent subsequent accepted turns. -/
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

/-- Bounded contention retry. Each attempt reloads and calls `prepare`; a
candidate computed from a stale image is never blindly reinstalled. -/
def receive (transport : Transport) (rootBytes : List UInt8 → Digest)
    (intent : DataIntent rootBytes) : Nat → IO (Result rootBytes)
  | 0 => pure .contention
  | attempts + 1 => do
      match ← load transport rootBytes with
      | .error message => return .unavailable message
      | .ok loaded =>
          match prepare loaded.image loaded.snapshot loaded.represented intent with
          | .inr (.replayed _) => return .confirmed .replayed loaded.snapshot
          | .inr (.rejected reason) => return .rejected reason
          | .inr _ => return .unavailable "unexpected complete-schedule outcome"
          | .inl _ =>
              let proposed := encode (loaded.image.append intent)
              match ← transport.cas (some loaded.bytes) proposed with
              | .installed | .alreadyPresent =>
                  confirm transport rootBytes intent .installed
              | .conflict => receive transport rootBytes intent attempts
              | .uncertain _ =>
                  confirm transport rootBytes intent .recoveredAfterUncertainResponse

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
