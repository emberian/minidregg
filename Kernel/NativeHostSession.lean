/-
One process-local resumed tip. `start` opens the Store the ordinary way — MAC'd
checkpoint plus suffix replay (`DurableReceiverIO.load`) — and validates it.
`refresh` asks the store for entries after the session's head: none means the
tip is current; new entries must continue the log chain, each carry a verifying
tag, and replay through the shared executor (`DurableReceiverIO.extendFrom`).
The advanced image is validated incrementally against the session's
(`validateLoadedFrom`, equal to `validateLoaded`); requests read the session's
`Opened`, never recompute its directory.
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
import Kernel.NativeObservationOpeningCache

namespace Minidregg.Kernel.NativeHostSession

open Minidregg.Compiler
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- The genesis-walked history of one physical image. -/
structure Walked (config : Config) where
  target : Durable
  verified : NativeHostReplay.Verified config target

structure Session (config : Config) where
  opened : Opened config
  openingCache : IO.Ref NativeObservationOpeningCache.Cache
  walked : Option (Walked config) := none
  /-- The light opening of the same Store (KN2): the ported operations are served
  from it (`NativeHost.submitRevokeLight`); refreshed with the full opening. -/
  light : NativeHostLight.Light config

/-- There is one process-local current image: the validated opening. Keeping a
second stored `durable` allowed exact readback adoption to move the semantic
walk while leaving the physical refresh predecessor behind. -/
def Session.durable {config : Config} (session : Session config) : Durable :=
  session.opened.durable

/-- Adopt only a receiver's exact CAS readback whose complete predecessor is
still this session's validated image. The already checked successor replaces
both the current opening and its admitted chronology; the next request still
calls `refresh` to read any concurrent suffix and current authority.

A delayed historical readback cannot move a newer session backward. Candidates,
ordinary confirmations and uncertain responses do not supply this witness. -/
def Session.rememberReadback {config : Config} (session : Session config)
    {store : DurableHistory.StoreIdentity} (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    {oldTarget : Durable} (old : NativeHostReplay.Verified config oldTarget)
    (readback : NativeHostReplay.ExactReadback config old) : Session config :=
  if session.durable.image = old.opened.durable.image then
    { session with
      opened := readback.after
      walked := some ⟨NativeHostReplay.exactCandidate old readback.derived readback.ready,
        NativeHostReplay.extendExact reader old readback⟩ }
  else session

/-- `rememberReadback` with the Reader of the Store at the readback's head (the walk
reads lifecycle history through it). A readback whose Reader cannot be minted is not
adopted: the session keeps its image and the next request's refresh reads the suffix. -/
def Session.rememberReadbackVia {config : Config} (session : Session config)
    {store : DurableHistory.StoreIdentity} (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    {oldTarget : Durable} (old : NativeHostReplay.Verified config oldTarget)
    (readback : NativeHostReplay.ExactReadback config old) : IO (Session config) := do
  match ← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes readback.after.durable with
  | .error _ => return session
  | .ok ⟨_, reader⟩ => return session.rememberReadback reader old readback

/-- The matched predecessor starts the next physical refresh at the exact
successor which the receiver already validated; it cannot reconstruct its own
just-committed entry a second time. -/
theorem Session.rememberReadback_opened {config : Config} (session : Session config)
    {store : DurableHistory.StoreIdentity} (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    {oldTarget : Durable} (old : NativeHostReplay.Verified config oldTarget)
    (readback : NativeHostReplay.ExactReadback config old)
    (current : session.durable.image = old.opened.durable.image) :
    (session.rememberReadback reader old readback).opened = readback.after := by
  simp only [Session.rememberReadback, if_pos current]

/-- The adoption is the exact receiver-created canonical successor, rather
than a cached root, projected state or independently provided candidate. -/
theorem Session.rememberReadback_image {config : Config} (session : Session config)
    {store : DurableHistory.StoreIdentity} (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    {oldTarget : Durable} (old : NativeHostReplay.Verified config oldTarget)
    (readback : NativeHostReplay.ExactReadback config old)
    (current : session.durable.image = old.opened.durable.image) :
    (session.rememberReadback reader old readback).durable.image =
      (NativeHostReplay.exactCandidate old readback.derived readback.ready).image := by
  unfold Session.durable
  rw [Session.rememberReadback_opened session reader old readback current]
  exact (NativeHostReplay.extendExact reader old readback).image_exact

/-- Every stale/forked predecessor leaves the entire newer session intact,
including current authority, chronology, and exact-byte opening cache. -/
theorem Session.rememberReadback_stale {config : Config} (session : Session config)
    {store : DurableHistory.StoreIdentity} (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    {oldTarget : Durable} (old : NativeHostReplay.Verified config oldTarget)
    (readback : NativeHostReplay.ExactReadback config old)
    (stale : session.durable.image ≠ old.opened.durable.image) :
    session.rememberReadback reader old readback = session := by
  simp only [Session.rememberReadback, if_neg stale]

/-- In particular a concurrent newer image defeats delayed historical
readback adoption. This regression ranges over every admitted readback. -/
theorem Session.rememberReadback_newer {config : Config} (session : Session config)
    {store : DurableHistory.StoreIdentity} (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    {oldTarget : Durable} (old : NativeHostReplay.Verified config oldTarget)
    (readback : NativeHostReplay.ExactReadback config old)
    (newer : old.opened.durable.height < session.durable.height) :
    session.rememberReadback reader old readback = session := by
  apply Session.rememberReadback_stale
  intro same
  have heights := congrArg (fun image : DurableReceiver.Image => image.accepted.length) same
  dsimp only at heights
  unfold DurableReceiverIO.Loaded.height at newer
  omega

/-- Rendering facts remain representation-only; all per-query scope/current
law checks still execute against the retained current validated opening. -/
theorem Session.rememberReadback_openingCache {config : Config} (session : Session config)
    {store : DurableHistory.StoreIdentity} (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    {oldTarget : Durable} (old : NativeHostReplay.Verified config oldTarget)
    (readback : NativeHostReplay.ExactReadback config old) :
    (session.rememberReadback reader old readback).openingCache = session.openingCache := by
  unfold Session.rememberReadback
  split <;> rfl


/-- info: 'Minidregg.Kernel.NativeHostSession.Session.rememberReadback_opened' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Session.rememberReadback_opened

/-- info: 'Minidregg.Kernel.NativeHostSession.Session.rememberReadback_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Session.rememberReadback_image

/-- info: 'Minidregg.Kernel.NativeHostSession.Session.rememberReadback_stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Session.rememberReadback_stale

/-- info: 'Minidregg.Kernel.NativeHostSession.Session.rememberReadback_newer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Session.rememberReadback_newer

/-- info: 'Minidregg.Kernel.NativeHostSession.Session.rememberReadback_openingCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Session.rememberReadback_openingCache

def start (config : Config) : IO (Except String (Session config)) := do
  match ← openExisting config with
  | .error detail => return .error detail
  | .ok opened =>
      match ← NativeHostLight.start config with
      | .error detail => return .error detail
      | .ok light =>
          let cache ← IO.mkRef ([] : NativeObservationOpeningCache.Cache)
          return .ok ⟨opened, cache, none, light⟩

def refresh (config : Config) (session : Session config) :
    IO (Except String (Session config)) := do
  match ← DurableReceiverIO.extendFrom config.transport ResourceBirthCodec.rootBytes
      session.durable with
  | .error detail => return .error detail
  | .ok ⟨durable, _⟩ =>
      -- The light opening reads the same new entries, verified as its open verifies them.
      let light ← match ← session.light.refresh with
        | .error detail => return .error detail
        | .ok light => pure light
      if durable.height = session.durable.height then
        return .ok { session with light }
      -- `validateLoadedFrom_eq`: the full validation, re-decoding and
      -- re-checking only the cells whose bytes the new records moved.
      match validateLoadedFrom config session.opened durable with
      | .error detail => return .error detail
      | .ok opened => return .ok { session with opened, light }

/-- The one semantic refresh routine. A retained exact tip extends only the
new authenticated suffix; a first provenance read starts at pinned genesis. -/
private def walkPhysical (config : Config) (prior : Option (Walked config))
    (physical : Durable) : IO (Except String (Walked config)) := do
  if let some retained := prior then
    if retained.target.height = physical.height then return .ok retained
  -- The walk reads lifecycle history through the Store's Reader at the physical head.
  let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes physical with
    | .error detail => return .error s!"semantic history reader: {detail}"
    | .ok sealed => pure sealed
  match prior with
  | some retained =>
      match ← NativeHostReplay.extendVerified config reader retained.verified physical with
      | .error failure =>
          return .error s!"semantic history refused at entry {failure.index}: {failure.detail}"
      | .ok verified => return .ok ⟨physical, verified⟩
  | none =>
      match ← NativeHostReplay.verifyLoaded config reader physical with
      | .error failure =>
          return .error s!"semantic history refused at entry {failure.index}: {failure.detail}"
      | .ok verified => return .ok ⟨physical, verified⟩

/-- The walk for an already physically refreshed session. -/
def walked (config : Config) (session : Session config) :
    IO (Except String (Walked config)) :=
  walkPhysical config session.walked session.durable

/-- Retain one admitted current opening and chronology together. -/
def Session.retainWalked {config : Config} (session : Session config)
    (current : Walked config) : Session config :=
  { session with opened := current.verified.opened, walked := some current }

/-- The retained opening is the complete physical target image checked by
semantic replay, including all source, authority and history records. -/
theorem Session.retainWalked_image {config : Config} (session : Session config)
    (current : Walked config) :
    (session.retainWalked current).durable.image = current.target.image :=
  current.verified.image_exact

/-- info: 'Minidregg.Kernel.NativeHostSession.Session.retainWalked_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Session.retainWalked_image

/-- A provenance request authenticates the physical suffix once, then uses
its re-admission walk's exact final opening. The ordinary refresh validates the
physical tip for families that do not need semantic replay; doing that first
here would validate the same final tip a second time immediately before the
walk validates each admitted prefix.

No current-authority fact is reused across an unseen suffix. Every new record
still passes Store chain/MAC/executor checks and fresh semantic re-admission at
its original height. With no new physical records, the existing exact walk is
returned without reconstruction. -/
def refreshWalked (config : Config) (session : Session config) :
    IO (Except String (Session config × Walked config)) := do
  let physical ← match ← DurableReceiverIO.extendFrom config.transport
      ResourceBirthCodec.rootBytes session.durable with
    | .error detail => return .error detail
    | .ok ⟨physical, _⟩ => pure physical
  let retained ← walkPhysical config session.walked physical
  match retained with
  | .error detail => return .error detail
  | .ok current =>
      return .ok (session.retainWalked current, current)

/-- A one-shot provenance request loads/authenticates the physical image,
then validates through its semantic walk. It does not construct an ordinary
session or validate the final tip redundantly before replay. -/
def startWalked (config : Config) : IO (Except String (Walked config)) := do
  match ← DurableReceiverIO.load config.transport ResourceBirthCodec.rootBytes with
  | .error detail => return .error detail
  | .ok physical => walkPhysical config none physical

end Minidregg.Kernel.NativeHostSession
