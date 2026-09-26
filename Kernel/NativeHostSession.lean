/-
One process-local verified tip. Every operation refreshes from the physical
store. Identical canonical bytes reuse the verifier-minted evidence; changed
bytes are accepted only by checked suffix extension. A failed read or changed
prefix poisons the caller's live session; only a fresh process can restart the
full semantic replay.

The configured signature helper must have stable semantics for this session.
Host.Main installs an executable snapshot in a private directory for the
stdio lifetime. That physical binding assumes the OS prevents modification of
the private snapshot by a different actor; cryptographic verifier correctness
and process transport remain the explicit native IO refinement boundary.
-/
import Kernel.NativeHost

namespace Minidregg.Kernel.NativeHostSession

open Minidregg.Compiler
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Session (config : Config) where
  target : Durable
  verified : NativeHostReplay.Verified config target

def Session.opened {config : Config} (session : Session config) : Opened config :=
  session.verified.opened

def start (config : Config) : IO (Except String (Session config)) := do
  match ← DurableReceiverIO.load config.storage.transport ResourceBirthCodec.rootBytes with
  | .error detail => return .error detail
  | .ok target =>
      match ← NativeHostReplay.verifyLoaded config target with
      | .error failure =>
          return .error s!"semantic history refused at entry {failure.index}: {failure.detail}"
      | .ok verified => return .ok ⟨target, verified⟩

def refresh (config : Config) (session : Session config) :
    IO (Except String (Session config)) := do
  match ← DurableReceiverIO.load config.storage.transport ResourceBirthCodec.rootBytes with
  | .error detail => return .error detail
  | .ok target =>
      if target.bytes == session.target.bytes then
        return .ok session
      match ← NativeHostReplay.extendVerified config session.verified target with
      | .error failure =>
          return .error s!"semantic history refused at entry {failure.index}: {failure.detail}"
      | .ok verified => return .ok ⟨target, verified⟩

end Minidregg.Kernel.NativeHostSession
