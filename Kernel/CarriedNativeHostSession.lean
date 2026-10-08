/- A separately typed process-local suffix certificate. Original genesis-walked
session evidence is never replaced or cast. The authenticated carry token mints
the initial state; each refresh really re-admits only its newly accepted suffix. -/
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.CarriedNativeHostSession

open Minidregg.Compiler
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Walked (config : Config) where
  anchor : Opened config
  target : Durable
  verified : NativeHostReplay.SuffixVerified config anchor target

def start (config : Config) (current : Durable)
    (custody : CarriedSegmentIO.PreservedPrefix config current) :
    IO (Except String (Walked config)) := do
  let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes current with
    | .error detail => return .error s!"carried history reader: {detail}"
    | .ok reader => pure reader
  match ← NativeHostReplay.verifyCarriedSuffixLoaded config reader current custody with
  | .error failure => return .error s!"carried history refused at {failure.index}: {failure.detail}"
  | .ok verified => return .ok ⟨custody.start, current, verified⟩

def refresh (config : Config) (prior : Walked config) (current : Durable) :
    IO (Except String (Walked config)) := do
  let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes current with
    | .error detail => return .error s!"carried history reader: {detail}"
    | .ok reader => pure reader
  match ← NativeHostReplay.extendSuffixVerified config reader prior.verified current with
  | .error failure => return .error s!"carried suffix refused at {failure.index}: {failure.detail}"
  | .ok verified => return .ok ⟨prior.anchor, current, verified⟩

end Minidregg.Kernel.CarriedNativeHostSession
