/-
One process-local resumed tip. `start` opens the light opening only: the MAC'd
checkpoint and the records after it (`DurableServed.openHead`), never the whole
log (KN2 stage 2b). `refresh` reads the entries after the session's head: none
means the tip is current; new entries must continue the log chain, each carry a
verifying tag, and replay through the shared executor (`Opening.extend`).
An operation not yet ported to the light opening asks for the full verified
materialization (`materialize`: the Store opened in full, `openExisting`); the
session keeps it and extends it with every later refresh (`extendFrom`, then
`validateLoadedFrom`, equal to `validateLoaded`), so requests read the session's
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
module

public import Kernel.NativeHost
public import Kernel.NativeObservationOpeningCache

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

namespace Minidregg.Kernel.NativeHostSession

open Minidregg.Compiler
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- The genesis-walked history of one physical image. -/
structure Walked (config : Config) where
  target : Durable
  verified : NativeHostReplay.Verified config target

structure Session (config : Config) where
  /-- The full verified materialization (KN2 stage 2a), opened only when an operation
  not yet ported to the light opening asks for it (`materialize`), then kept and
  refreshed with the session. A session that serves only ported operations never
  opens it: its start and refresh read the light opening alone. -/
  full : Option (Opened config) := none
  openingCache : IO.Ref NativeObservationOpeningCache.Cache
  walked : Option (Walked config) := none
  /-- The light opening of the Store (KN2): the ported operations are served from it
  (`NativeHost.submitRevokeLight`); every request refreshes it. -/
  light : NativeHostLight.Light config

/-- The full image, where this session has opened it. There is at most one
process-local full image: exact readback adoption replaces it, never a second
stored `durable` beside it (that let a readback move the semantic walk while
leaving the physical refresh predecessor behind). -/
def Session.durable? {config : Config} (session : Session config) : Option Durable :=
  session.full.map (·.durable)

/-- Adopt only a receiver's exact CAS readback whose complete predecessor is
still this session's validated full image. The already checked successor
replaces both the full opening and its admitted chronology; the next request
still calls `refresh` to read any concurrent suffix and current authority.

A delayed historical readback cannot move a newer session backward, and a
session that holds no full image adopts none. Candidates, ordinary
confirmations and uncertain responses do not supply this witness. -/
def Session.rememberReadback {config : Config} (session : Session config)
    {store : DurableHistory.StoreIdentity} (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    {oldTarget : Durable} (old : NativeHostReplay.Verified config oldTarget)
    (readback : NativeHostReplay.ExactReadback config old) : Session config :=
  if session.durable?.map (·.image) = some old.opened.durable.image then
    { session with
      full := some readback.after
      walked := some ⟨NativeHostReplay.exactCandidate old readback.derived readback.ready readback.tag,
        NativeHostReplay.extendExact reader old readback⟩ }
  else session

/-- `rememberReadback` with the Reader of the Store at the readback's head (the walk
reads lifecycle history through it). A readback whose Reader cannot be minted is not
adopted: the session keeps its image and the next request's refresh reads the suffix. -/
def Session.rememberReadbackVia {config : Config} (session : Session config)
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
    (current : session.durable?.map (·.image) = some old.opened.durable.image) :
    (session.rememberReadback reader old readback).full = some readback.after := by
  simp only [Session.rememberReadback, if_pos current]

/-- The adoption is the exact receiver-created canonical successor, rather
than a cached root, projected state or independently provided candidate. -/
theorem Session.rememberReadback_image {config : Config} (session : Session config)
    {store : DurableHistory.StoreIdentity} (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    {oldTarget : Durable} (old : NativeHostReplay.Verified config oldTarget)
    (readback : NativeHostReplay.ExactReadback config old)
    (current : session.durable?.map (·.image) = some old.opened.durable.image) :
    (session.rememberReadback reader old readback).durable?.map (·.image) =
      some (NativeHostReplay.exactCandidate old readback.derived readback.ready readback.tag).image := by
  unfold Session.durable?
  rw [Session.rememberReadback_opened session reader old readback current]
  exact congrArg some (NativeHostReplay.extendExact reader old readback).image_exact

/-- Every stale/forked predecessor, and a session holding no full image, leaves the
entire session intact, including current authority, chronology, and exact-byte
opening cache. -/
theorem Session.rememberReadback_stale {config : Config} (session : Session config)
    {store : DurableHistory.StoreIdentity} (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    {oldTarget : Durable} (old : NativeHostReplay.Verified config oldTarget)
    (readback : NativeHostReplay.ExactReadback config old)
    (stale : session.durable?.map (·.image) ≠ some old.opened.durable.image) :
    session.rememberReadback reader old readback = session := by
  simp only [Session.rememberReadback, if_neg stale]

/-- In particular a concurrent newer image defeats delayed historical
readback adoption. This regression ranges over every admitted readback. -/
theorem Session.rememberReadback_newer {config : Config} (session : Session config)
    {store : DurableHistory.StoreIdentity} (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    {oldTarget : Durable} (old : NativeHostReplay.Verified config oldTarget)
    (readback : NativeHostReplay.ExactReadback config old) {durable : Durable}
    (held : session.durable? = some durable)
    (newer : old.opened.durable.height < durable.height) :
    session.rememberReadback reader old readback = session := by
  apply Session.rememberReadback_stale
  intro same
  rw [held] at same
  have heights := congrArg (fun image : DurableReceiver.Image => image.accepted.length)
    (Option.some.inj same)
  simp only [DurableReceiverIO.Loaded.height_eq] at newer
  simp only at heights
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

/-- A session opens the light opening only: the checkpoint and the records after it
(`DurableServed.openHead`), never the whole log. -/
def start (config : Config) : IO (Except String (Session config)) := do
  match ← NativeHostLight.start config with
  | .error detail => return .error detail
  | .ok light =>
      let cache ← IO.mkRef ([] : NativeObservationOpeningCache.Cache)
      return .ok { openingCache := cache, light }

/-- The light opening is refreshed on every request (`Light.refresh`: the entries
another writer appended, verified as the open verifies them). The full image, where
the session holds one, is extended by the same entries and validated incrementally
(`validateLoadedFrom`, equal to `validateLoaded`). -/
def refresh (config : Config) (session : Session config) :
    IO (Except String (Session config)) := do
  let light ← match ← session.light.refresh with
    | .error detail => return .error detail
    | .ok light => pure light
  let some opened := session.full
    | return .ok { session with light }
  match ← DurableReceiverIO.extendFrom config.transport ResourceBirthCodec.rootBytes
      opened.durable with
  | .error detail => return .error detail
  | .ok ⟨durable, _⟩ =>
      if durable.height = opened.durable.height then
        return .ok { session with light }
      -- `validateLoadedFrom_eq`: the full validation, re-decoding and
      -- re-checking only the cells whose bytes the new records moved.
      match validateLoadedFrom config opened durable with
      | .error detail => return .error detail
      | .ok opened => return .ok { session with full := some opened, light }

/-- The full image of an already refreshed session: the one it holds, or the Store
opened in full now (`openExisting`) and kept. -/
def materialize (config : Config) (session : Session config) :
    IO (Except String (Session config × Opened config)) := do
  match session.full with
  | some opened => return .ok (session, opened)
  | none =>
      match ← openExisting config with
      | .error detail => return .error detail
      | .ok opened => return .ok ({ session with full := some opened }, opened)

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
      match ← NativeHostReplay.verifyStart config reader physical with
      | .error failure =>
          return .error s!"semantic history refused at entry {failure.index}: {failure.detail}"
      | .ok verified => return .ok ⟨physical, verified⟩

/-- The walk for an already physically refreshed session: over its full image, the
Store opened in full when it holds none. -/
def walked (config : Config) (session : Session config) :
    IO (Except String (Walked config)) := do
  match session.full with
  | some opened => walkPhysical config session.walked opened.durable
  | none =>
      match ← DurableReceiverIO.load config.transport ResourceBirthCodec.rootBytes with
      | .error detail => return .error detail
      | .ok physical => walkPhysical config session.walked physical

/-- Retain one admitted current opening and chronology together. -/
def Session.retainWalked {config : Config} (session : Session config)
    (current : Walked config) : Session config :=
  { session with full := some current.verified.opened, walked := some current }

/-- The retained opening is the complete physical target image checked by
semantic replay, including all source, authority and history records. -/
theorem Session.retainWalked_image {config : Config} (session : Session config)
    (current : Walked config) :
    (session.retainWalked current).durable?.map (·.image) = some current.target.image :=
  congrArg some current.verified.image_exact

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
  -- A retained walk reads only the entries after ITS target (`extendFrom`), and that read's
  -- append proof extends it (`extendVerifiedAppended`): no re-encoding and comparison of the
  -- whole accepted prefix (`extendVerified`, O(history) on every growth; law 17).
  if let some held := session.walked then
    match ← DurableReceiverIO.extendFrom config.transport ResourceBirthCodec.rootBytes held.target with
    | .error detail => return .error detail
    | .ok ⟨physical, seedExact, acceptedExact, _⟩ =>
        if physical.height = held.target.height then
          return .ok (session.retainWalked held, held)
        let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf config.transport
            ResourceBirthCodec.rootBytes physical with
          | .error detail => return .error s!"semantic history reader: {detail}"
          | .ok sealed => pure sealed
        match ← NativeHostReplay.extendVerifiedAppended config reader held.verified physical
            seedExact acceptedExact with
        | .error failure =>
            return .error s!"semantic history refused at entry {failure.index}: {failure.detail}"
        | .ok verified =>
            let current : Walked config := ⟨physical, verified⟩
            return .ok (session.retainWalked current, current)
  let physical ← match session.full with
    | some opened =>
        match ← DurableReceiverIO.extendFrom config.transport ResourceBirthCodec.rootBytes
            opened.durable with
        | .error detail => return .error detail
        | .ok ⟨physical, _⟩ => pure physical
    | none =>
        match ← DurableReceiverIO.load config.transport ResourceBirthCodec.rootBytes with
        | .error detail => return .error detail
        | .ok physical => pure physical
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
