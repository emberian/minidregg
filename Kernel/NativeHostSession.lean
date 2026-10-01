/-
One process-local resumed tip. `start` opens the Store the ordinary way — MAC'd
checkpoint plus suffix replay (`DurableReceiverIO.load`) — and validates it.
`refresh` asks the store for entries after the session's head: none means the
tip is current; new entries must continue the log chain, each carry a
verifying tag, and replay through the shared executor (`DurableReceiverIO.extendFrom`).
A failed read, a shrunk log or a refused entry poisons the session.

The walk-provenance families (application lifecycle, dispatch, grain session
enrollment, fn frontier) admit new work from certificates that only the genesis
re-admission walk mints (`NativeHostReplay.Verified`). The session computes
that walk lazily, on the first such request, and extends it by re-admitting
each later record; ordinary operations never pay for it.

The configured signature helper must have stable semantics for this session.
Host.Main installs an executable snapshot in a private directory for the
stdio lifetime.
-/
import Kernel.NativeHost

namespace Minidregg.Kernel.NativeHostSession

open Minidregg.Compiler
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- The genesis-walked history of one physical image. -/
structure Walked (config : Config) where
  target : Durable
  verified : NativeHostReplay.Verified config target

structure Session (config : Config) where
  durable : Durable
  opened : Opened config
  walked : Option (Walked config) := none

def start (config : Config) : IO (Except String (Session config)) := do
  match ← openExisting config with
  | .error detail => return .error detail
  | .ok opened => return .ok ⟨opened.durable, opened, none⟩

def refresh (config : Config) (session : Session config) :
    IO (Except String (Session config)) := do
  match ← DurableReceiverIO.extendFrom config.transport ResourceBirthCodec.rootBytes
      session.durable with
  | .error detail => return .error detail
  | .ok durable =>
      if durable.image.accepted.length = session.durable.image.accepted.length then
        return .ok session
      match validateLoaded config durable with
      | .error detail => return .error detail
      | .ok opened => return .ok { session with durable, opened }

/-- The walk for the session's current image: extend the retained walk by the
records appended since, or walk from genesis the first time. -/
def walked (config : Config) (session : Session config) :
    IO (Except String (Walked config)) := do
  match session.walked with
  | some prior =>
      if prior.target.image.accepted.length = session.durable.image.accepted.length then
        return .ok prior
      match ← NativeHostReplay.extendVerified config prior.verified session.durable with
      | .error failure =>
          return .error s!"semantic history refused at entry {failure.index}: {failure.detail}"
      | .ok verified => return .ok ⟨session.durable, verified⟩
  | none =>
      match ← NativeHostReplay.verifyLoaded config session.durable with
      | .error failure =>
          return .error s!"semantic history refused at entry {failure.index}: {failure.detail}"
      | .ok verified => return .ok ⟨session.durable, verified⟩

/-- A one-shot process that needs only the walked history. -/
def startWalked (config : Config) : IO (Except String (Walked config)) := do
  match ← start config with
  | .error detail => return .error detail
  | .ok session => walked config session

end Minidregg.Kernel.NativeHostSession
