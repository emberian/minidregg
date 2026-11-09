/-
# Compiler.DurableNodeCache — the serving Store's node rows, held in the Host

Row 37 of docs/PERF-CLIENT.md: every append read each changed key's 48-level index path and its
siblings back from SQLite through the Store helper (`DurableReceiverIO.indexRows`), and every
request's footprint read its declared keys' paths the same way (`DurableHistoryStore.byTx`,
`spent`), although the serving Host wrote every one of those rows itself.

`cached` wraps a transport's `history` and `append`. The Store keeps every node row versioned by
the height that wrote it, and a read names a height and gets each row's latest version at or below
it. So the rows at a committed height never change, and an append the Store installed at
`h + 1` changes exactly the rows it wrote. The cache holds the rows at one height, as this
process wrote or read them there (an absent row included), and moves to the next height by the
rows of the append it installed. A read at the cache's height is answered from it, and only
its misses go to the Store; a read at any other height, or one that names entries, goes to the
Store unchanged. Every row a reader uses is verified against the authenticated roots, as a row
read from the Store is (`indexRows`, `DurableHistoryStore.fetch`), so the cache is not trusted.

Only the serving Store Host turns it on (`enable`, for its own Store's root): a reader of a Store
another process appends to keeps reading the Store.
-/
module

public import Compiler.DurableReceiverCore

@[expose] public section

namespace Minidregg.Compiler.DurableNodeCache

open Minidregg.Compiler.DurableReceiverIO

set_option autoImplicit false

/-- A node's latest version at or below the cache's height (`none`: no row there), its key and
value packed. -/
abbrev Version := Option (Nat × ByteArray)

/-- One Store's node rows at `height`. -/
structure Rows where
  height : Nat
  rows : Std.HashMap (Nat × ByteArray) Version

/-- The Store root this process serves (the cache is off for every other root), and its rows. -/
initialize served : IO.Ref (Option (String × Option Rows)) ← IO.mkRef none

/-- Hold the node rows of the Store at `root`, the one this process appends to. -/
def enable (root : String) : IO Unit := served.set (some (root, none))

private def unpack (version : Version) :=
  version.map fun (height, value) => (height, value.toList)

/-- `history`, answered at the cache's height from the rows it holds. -/
def history (root : String) (inner : HistoryRequest → IO (Except String HistoryRead))
    (request : HistoryRequest) : IO (Except String HistoryRead) := do
  if !request.heights.isEmpty then return ← inner request
  -- The misses are listed inside `modifyGet`, so no reference to the held map outlives it (a
  -- `get` kept one alive across the fetch, and the learning inserts below then copied the map).
  let misses? ← served.modifyGet fun current =>
    match current with
    | some (root', some cache) =>
        if root' = root ∧ cache.height = request.atHeight then
          (some (request.nodes.filter fun (space, key) => !cache.rows.contains (space, key.toByteArray)),
            some (root', some cache))
        else (none, some (root', some cache))
    | other => (none, other)
  let some misses := misses? | inner request
  let fetched ← if misses.isEmpty then pure (.ok ⟨request.atHeight, [], []⟩)
    else inner { request with nodes := misses }
  match fetched with
  | .error message => return .error message
  | .ok read =>
      -- Learn the fetched rows and answer inside one `modifyGet`, where the held map is not
      -- shared, so the inserts update it in place rather than copying it per request.
      let answered ← served.modifyGet fun current =>
        match current with
        | some (root', some held) =>
            if root' = root ∧ held.height = request.atHeight then
              let learned := read.nodes.foldl (init := held.rows) fun rows (space, key, version) =>
                rows.insert (space, key.toByteArray) (version.map fun (height, value) => (height, value.toByteArray))
              let nodes := request.nodes.map fun (space, key) =>
                (space, key, unpack ((learned.get? (space, key.toByteArray)).getD none))
              (some nodes, some (root', some ⟨held.height, learned⟩))
            else (none, some (root', some held))
        | other => (none, other)
      match answered with
      | some nodes => return .ok ⟨max read.head request.atHeight, read.entries, nodes⟩
      | none => inner request

/-- `append`; an append the Store installed moves the cache to its height by the rows it wrote
(a fresh cache when the cache was not at the height below). Any other outcome drops the cache. -/
def append (root : String) (inner : Nat → Entry → List NodeWrite → IO CasObservation)
    (height : Nat) (entry : Entry) (nodes : List NodeWrite) : IO CasObservation := do
  let observed ← inner height entry nodes
  served.modify fun current =>
    match current with
    | some (root', held) =>
        if root' ≠ root then current
        else match observed with
          | .installed =>
              let base := match held with
                | some cache => if cache.height + 1 = height then cache.rows else {}
                | none => {}
              some (root', some ⟨height, nodes.foldl (init := base) fun rows node =>
                rows.insert (node.space, node.key.toByteArray) (some (height, node.value.toByteArray))⟩)
          | _ => some (root', none)
    | none => none
  return observed

/-! ## The decoded index rows

Above the node rows, the serving Host holds the index trie's rows decoded, by bit prefix, at one
height: the rows its appends wrote (handed over by `DurableServed.receiveServed`, which has them
decoded) and the rows its reads decoded. An index answer at that height walks them directly
(`DurableReceiverIO.withIndexRows`), with no prefix list, no row key and no decode; a walk they
cannot verify falls back to the Store read. The same height discipline as the node rows: an
append at `h + 1` writes exactly the rows that change, so every other row held at `h` stands. -/

/-- Decoded index rows at `height`. -/
structure Decoded where
  height : Nat
  rows : Std.HashMap (List Bool) DurableIndex.Row

initialize decoded : IO.Ref (Option (String × Decoded)) ← IO.mkRef none

/-- The decoded rows held for `root` at `height`. -/
def heldIndexRows (root : String) (height : Nat) : IO (Option (List Bool → Option DurableIndex.Row)) := do
  let some (root', held) ← decoded.get | return none
  if root' = root ∧ held.height = height then
    let rows := held.rows
    return some fun path => rows.get? path
  else return none

/-- Hold rows for `root`: an append's writes move the held rows from `height - 1` (a fresh set
when they were not there); rows read join the set at their height, or start one above it. -/
def holdIndexRows (root : String) (height : Nat) (appended : Bool)
    (rows : List (List Bool × DurableIndex.Row)) : IO Unit :=
  let onto (base : Std.HashMap (List Bool) DurableIndex.Row) : Option (String × Decoded) :=
    some (root, ⟨height, rows.foldl (init := base) fun map row => map.insert row.1 row.2⟩)
  -- One match that moves the held map, so an insert updates it in place.
  decoded.modify fun current =>
    match current with
    | some (root', held) =>
        if root' ≠ root then onto {}
        else if appended then onto (if held.height + 1 = height then held.rows else {})
        else if held.height = height then onto held.rows
        else if held.height > height then some (root', held)
        else onto {}
    | none => onto {}

/-- `transport` with its node rows held for `root` (`history`, `append`), and its decoded index
rows (`heldIndexRows`, `holdIndexRows`). -/
def cached (root : String) (transport : Transport) : Transport :=
  { transport with
    history := history root transport.history
    append := append root transport.append
    heldIndexRows := heldIndexRows root
    holdIndexRows := holdIndexRows root
    preloadsIndex := true }

end Minidregg.Compiler.DurableNodeCache
