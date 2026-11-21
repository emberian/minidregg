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
height: the rows its appends wrote (handed over by `DurableServed.receiveServed` and by the
receiving loop's `DurableReceiverIO.publishAfter`, which have them decoded) and the rows its reads
decoded. An index answer at that height walks them directly
(`DurableReceiverIO.withIndexRows`), with no prefix list, no row key and no decode; a walk they
cannot verify falls back to the Store read. The same height discipline as the node rows: an
append at `h + 1` writes exactly the rows that change, so every other row held at `h` stands. -/

/-- Decoded index rows by bit prefix: a persistent binary trie over the prefixes themselves. A
lookup or an insert follows the prefix's bits and compares no key (an ordered map of bit lists
compared a dozen whole prefixes per row, three hundred rows an append). Persistent: a request's
lookup function (`heldIndexRows`) still holds the rows when its own append hands over the rows it
wrote, so an insert must not copy the set. A hash map shared that way was copied whole on every
`op 2` (the preloaded trie: ~20 ms at ~6,000 records, until an append from elsewhere reset it to
a small set). -/
inductive Held where
  | empty
  | node (row : Option DurableIndex.Row) (left right : Held)

/-- The row held at a prefix. -/
def Held.get? : Held → List Bool → Option DurableIndex.Row
  | .empty, _ => none
  | .node row _ _, [] => row
  | .node _ left right, bit :: rest => if bit then right.get? rest else left.get? rest

/-- Hold `row` at a prefix (over the row held there). -/
def Held.insert : Held → List Bool → DurableIndex.Row → Held
  | .empty, [], row => .node (some row) .empty .empty
  | .node _ left right, [], row => .node (some row) left right
  | .empty, bit :: rest, row =>
      if bit then .node none .empty (Held.empty.insert rest row)
      else .node none (Held.empty.insert rest row) .empty
  | .node held left right, bit :: rest, row =>
      if bit then .node held left (right.insert rest row) else .node held (left.insert rest row) right

theorem Held.get?_insert : ∀ (held : Held) (path : List Bool) (row : DurableIndex.Row)
    (other : List Bool),
    (held.insert path row).get? other = if path = other then some row else held.get? other
  | .empty, [], _, [] => by simp [Held.insert, Held.get?]
  | .empty, [], _, _ :: _ => by simp [Held.insert, Held.get?]
  | .node _ _ _, [], _, [] => by simp [Held.insert, Held.get?]
  | .node _ _ _, [], _, _ :: _ => by simp [Held.insert, Held.get?]
  | .empty, bit :: _, _, [] => by cases bit <;> simp [Held.insert, Held.get?]
  | .node _ _ _, bit :: _, _, [] => by cases bit <;> simp [Held.insert, Held.get?]
  | .empty, bit :: rest, row, b :: others => by
      have ih := Held.get?_insert .empty rest row others
      cases bit <;> cases b <;> simp [Held.insert, Held.get?, ih]
  | .node _ left right, bit :: rest, row, b :: others => by
      have ihl := Held.get?_insert left rest row others
      have ihr := Held.get?_insert right rest row others
      cases bit <;> cases b <;> simp [Held.insert, Held.get?, ihl, ihr]

/-- Decoded index rows at `height`. -/
structure Decoded where
  height : Nat
  rows : Held

/-- The holder after `rows` are handed to it at `height` (the step `holdIndexRows` makes on one
Store's holder). An append's writes (`appended`) move the held rows from `height - 1`, and start
a fresh set when the holder was not there. Rows read join the set at their height, start one
above it, and are dropped below it. Among `rows` the first of a prefix wins, as in
`DurableIndex.overlay`, the Store's view after an append in every index statement. -/
def Decoded.hold (current : Option Decoded) (height : Nat) (appended : Bool)
    (rows : List (List Bool × DurableIndex.Row)) : Option Decoded :=
  let onto (base : Held) : Option Decoded :=
    some ⟨height, rows.foldr (fun row map => map.insert row.1 row.2) base⟩
  match current with
  | some held =>
      if appended then onto (if held.height + 1 = height then held.rows else .empty)
      else if held.height = height then onto held.rows
      else if held.height > height then some held
      else onto .empty
  | none => onto .empty

/-! ### The holder's invariant

The Store's index rows are modelled by height (`store h p`: the latest version of the row at
prefix `p` at or below `h`, which is what a read at `h` returns). The append the Store installs
at `h + 1` with rows `written` makes `store (h + 1) = DurableIndex.overlay (store h) written`:
the transport's contract, and the form every index statement uses (`DurableIndex.SetPreserves`,
`maintained_apply`). The holder is a part of the Store's rows, never more: `Faithful`. A walk
through a faithful holder that meets no missing row is the walk through the Store
(`lookupRows_eq_of_faithful`); a holder handed the rows of an append the Store did not install
is not faithful and answers a lookup wrongly (`hold_unconfirmed_wrong`). Uses stay verified
against the authenticated root either way (`DurableReceiverIO.withIndexRows`): faithfulness is
what makes the holder answer, not what makes an answer sound. -/

/-- Every row held is the Store's row at the held height. -/
def Decoded.Faithful (store : Nat → List Bool → Option DurableIndex.Row) (held : Decoded) : Prop :=
  ∀ path row, held.rows.get? path = some row → store held.height path = some row

/-- A holder (or none) is faithful. -/
def HeldFaithful (store : Nat → List Bool → Option DurableIndex.Row) (held : Option Decoded) : Prop :=
  ∀ decoded, held = some decoded → decoded.Faithful store

/-- Handing rows onto a set is `DurableIndex.overlay` over it. -/
theorem foldr_insert_eq_overlay (rows : List (List Bool × DurableIndex.Row))
    (base : Held) (path : List Bool) :
    (rows.foldr (fun row map => map.insert row.1 row.2) base).get? path =
      DurableIndex.overlay (fun p => base.get? p) rows path := by
  induction rows with
  | nil => simp [DurableIndex.overlay]
  | cons first rest ih =>
      rw [List.foldr_cons, Held.get?_insert]
      by_cases same : first.1 = path
      · simp [DurableIndex.overlay, same]
      · simp only [same, ↓reduceIte]
        rw [ih]
        simp [DurableIndex.overlay, same]

/-- Rows overlaid on a part of `under` are a part of the same rows overlaid on `under`. -/
theorem overlay_part {base under : List Bool → Option DurableIndex.Row}
    (part : ∀ path row, base path = some row → under path = some row)
    (rows : List (List Bool × DurableIndex.Row)) (path : List Bool) (row : DurableIndex.Row)
    (found : DurableIndex.overlay base rows path = some row) :
    DurableIndex.overlay under rows path = some row := by
  unfold DurableIndex.overlay at found ⊢
  split at found
  · exact found
  · exact part path row found

/-- **The hand-over preserves the invariant.** When the Store installed at `height + 1` an append
whose index rows are `rows`, the holder handed those rows is faithful: moved from `height`, or
started fresh. -/
theorem Decoded.hold_appended {store : Nat → List Bool → Option DurableIndex.Row}
    {current : Option Decoded} (faithful : HeldFaithful store current) (height : Nat)
    (rows : List (List Bool × DurableIndex.Row))
    (installed : store (height + 1) = DurableIndex.overlay (store height) rows) :
    HeldFaithful store (Decoded.hold current (height + 1) true rows) := by
  have fresh : HeldFaithful store (some ⟨height + 1, rows.foldr (fun row map => map.insert row.1 row.2) .empty⟩) := by
    intro decoded eq path row held
    cases Option.some.inj eq
    rw [foldr_insert_eq_overlay] at held
    show store (height + 1) path = some row
    rw [installed]
    exact overlay_part (base := fun p => Held.empty.get? p)
      (fun p r h => by simp [Held.get?] at h) rows path row held
  cases current with
  | none => exact fresh
  | some held =>
      by_cases adjacent : held.height + 1 = height + 1
      · intro decoded eq path row found
        simp only [Decoded.hold, ite_true, adjacent] at eq
        cases Option.some.inj eq
        rw [foldr_insert_eq_overlay] at found
        show store (height + 1) path = some row
        rw [installed]
        have at_ : held.height = height := Nat.succ.inj adjacent
        exact overlay_part (fun p r h => at_ ▸ faithful held rfl p r h) rows path row found
      · simpa only [Decoded.hold, ite_true, adjacent, ite_false] using fresh

/-- **Rows read from the Store keep the invariant**: rows the Store holds at `height` join the
holder at that height, start one above it, and leave a holder above them as it was. -/
theorem Decoded.hold_read {store : Nat → List Bool → Option DurableIndex.Row}
    {current : Option Decoded} (faithful : HeldFaithful store current) (height : Nat)
    (rows : List (List Bool × DurableIndex.Row))
    (read : ∀ entry ∈ rows, store height entry.1 = some entry.2) :
    HeldFaithful store (Decoded.hold current height false rows) := by
  have onto : ∀ base : Held,
      (∀ path row, base.get? path = some row → store height path = some row) →
      HeldFaithful store (some ⟨height, rows.foldr (fun row map => map.insert row.1 row.2) base⟩) := by
    intro base part decoded eq path row found
    cases Option.some.inj eq
    rw [foldr_insert_eq_overlay] at found
    show store height path = some row
    unfold DurableIndex.overlay at found
    split at found
    · next entry row' hit =>
        have member := List.mem_of_find?_eq_some hit
        have here : entry = path := by simpa using List.find?_some hit
        have stored := read _ member
        cases Option.some.inj found
        simpa [here] using stored
    · exact part path row found
  have fresh := onto .empty (fun p r h => by simp [Held.get?] at h)
  cases current with
  | none => exact fresh
  | some held =>
      by_cases same : held.height = height
      · have joined := onto held.rows (fun p r h => same ▸ faithful held rfl p r h)
        simpa only [Decoded.hold, Bool.false_eq_true, ite_false, same, ite_true] using joined
      · by_cases above : held.height > height
        · simpa only [Decoded.hold, Bool.false_eq_true, ite_false, same, above, ite_true] using faithful
        · simpa only [Decoded.hold, Bool.false_eq_true, ite_false, same, above] using fresh

/-- Whether the walk for `bits` meets a prefix under a non-empty digest whose row `rows` lacks. -/
def walkMisses (rows : List Bool → Option DurableIndex.Row) (bits : List Bool) :
    Nat → List Bool → Minidregg.Theory.TypedAuthorization.Digest → Bool
  | 0, _, _ => false
  | fuel + 1, here, expected =>
      if expected = DurableIndex.emptyDigest then false else
      match rows here with
      | none => true
      | some (.leaf _ _) => false
      | some (.branch l r) =>
          match bits[here.length]? with
          | none => false
          | some bit => walkMisses rows bits fuel (here ++ [bit]) (if bit then r else l)

/-- A walk through a part of the Store's rows that lacks no row it meets is the Store's walk. -/
theorem walk_eq_of_part {held store : List Bool → Option DurableIndex.Row}
    (part : ∀ path row, held path = some row → store path = some row) (bits : List Bool) :
    ∀ (fuel : Nat) (here : List Bool) (expected : Minidregg.Theory.TypedAuthorization.Digest) (siblings : List Minidregg.Theory.TypedAuthorization.Digest),
      walkMisses held bits fuel here expected = false →
      DurableIndex.walk held bits fuel here expected siblings =
        DurableIndex.walk store bits fuel here expected siblings
  | 0, _, _, _, _ => rfl
  | fuel + 1, here, expected, siblings, complete => by
      unfold walkMisses at complete
      unfold DurableIndex.walk
      by_cases empty : expected = DurableIndex.emptyDigest
      · simp only [empty, ite_true]
      · simp only [empty, ite_false] at complete ⊢
        cases row : held here with
        | none => simp [row] at complete
        | some found =>
            rw [part here found row]
            cases found with
            | leaf k v => rfl
            | branch l r =>
                simp only [row] at complete
                cases bit : bits[here.length]? with
                | none => rfl
                | some b =>
                    simp only [bit] at complete
                    exact walk_eq_of_part part bits fuel _ _ _ complete

/-- **Every lookup a faithful holder can answer is the Store's lookup**: at the held height,
the verified lookup of `k` through the held rows is the verified lookup through the Store's
rows, whenever the held rows lack no row on `k`'s walk. -/
theorem lookupRows_eq_of_faithful {store : Nat → List Bool → Option DurableIndex.Row}
    {held : Decoded} (faithful : held.Faithful store) (root : Minidregg.Theory.TypedAuthorization.Digest)
    (k : DurableIndex.IndexKey)
    (complete : walkMisses (fun path => held.rows.get? path) (DurableIndex.bitsOf k) 521 [] root = false) :
    DurableIndex.lookupRows (fun path => held.rows.get? path) root k =
      DurableIndex.lookupRows (store held.height) root k := by
  have same : DurableIndex.openingOf (fun path => held.rows.get? path) root k =
      DurableIndex.openingOf (store held.height) root k :=
    walk_eq_of_part faithful _ 521 [] root [] complete
  unfold DurableIndex.lookupRows
  simp only [same]

/-- **Satisfiable**: a holder that holds a row is faithful to a Store that installed it. -/
theorem faithful_inhabited (row : DurableIndex.Row) :
    ∃ (store : Nat → List Bool → Option DurableIndex.Row) (held : Option Decoded),
      HeldFaithful store held ∧ ∃ decoded, held = some decoded ∧ decoded.rows.get? [] = some row := by
  let store : Nat → List Bool → Option DurableIndex.Row := fun height =>
    if height = 0 then fun _ => none else DurableIndex.overlay (fun _ => none) [([], row)]
  refine ⟨store, Decoded.hold none 1 true [([], row)],
    Decoded.hold_appended (store := store) (current := none) (fun _ eq => by cases eq) 0 _ rfl,
    _, rfl, ?_⟩
  rw [foldr_insert_eq_overlay]
  simp [DurableIndex.overlay]

/-- **Teeth**: the hand-over's premise is needed. A holder handed the rows of an append the
Store did not install (here the Store holds no row at all) is not faithful, and under any
non-empty root its walk claims the key present where the Store's walk finds nothing. -/
theorem Decoded.hold_unconfirmed_wrong (k : DurableIndex.IndexKey) (root : Minidregg.Theory.TypedAuthorization.Digest)
    (nonEmpty : root ≠ DurableIndex.emptyDigest) :
    ∃ (store : Nat → List Bool → Option DurableIndex.Row) (decoded : Decoded),
      HeldFaithful store none ∧
      Decoded.hold none 1 true [([], .leaf k [])] = some decoded ∧
      store 1 ≠ DurableIndex.overlay (store 0) [([], .leaf k [])] ∧
      ¬ decoded.Faithful store ∧
      (DurableIndex.openingOf (fun path => decoded.rows.get? path) root k).claims k = some [] ∧
      (DurableIndex.openingOf (store decoded.height) root k).claims k = none := by
  have held : (([([], DurableIndex.Row.leaf k [])] : List (List Bool × DurableIndex.Row)).foldr
      (fun row map => map.insert row.1 row.2) Held.empty).get? [] = some (.leaf k []) := by
    rw [foldr_insert_eq_overlay]
    simp [DurableIndex.overlay]
  refine ⟨fun _ _ => none, _, (fun _ eq => by cases eq), rfl, ?_, ?_, ?_, ?_⟩
  · intro same
    have := congrFun same []
    simp [DurableIndex.overlay] at this
  · intro faithful
    have := faithful [] _ held
    simp at this
  · show (DurableIndex.walk _ (DurableIndex.bitsOf k) (520 + 1) [] root []).claims k = some []
    unfold DurableIndex.walk
    simp only [nonEmpty, ite_false, List.length_nil]
    rw [held]
    simp [DurableIndex.Opening.claims]
  · show (DurableIndex.walk _ (DurableIndex.bitsOf k) (520 + 1) [] root []).claims k = none
    unfold DurableIndex.walk
    simp [nonEmpty, DurableIndex.Opening.claims]

#assert_axioms Held.get?_insert foldr_insert_eq_overlay Decoded.hold_appended Decoded.hold_read walk_eq_of_part
  lookupRows_eq_of_faithful faithful_inhabited Decoded.hold_unconfirmed_wrong

/-- The decoded rows held, by Store root: a process that appends to several Stores (the four
sources of one fixture process) holds each one's rows, where one slot made every append evict
the others' and read its rows from the Store again. -/
initialize decoded : IO.Ref (Std.HashMap String Decoded) ← IO.mkRef {}

/-- The decoded rows held for `root` at `height`. -/
def heldIndexRows (root : String) (height : Nat) : IO (Option (List Bool → Option DurableIndex.Row)) := do
  let some held := (← decoded.get)[root]? | return none
  if held.height = height then
    let rows := held.rows
    return some fun path => rows.get? path
  else return none

/-- Hold rows for `root` (`Decoded.hold` on that Store's holder). An append's rows are handed
over only for an append the Store installed (`Decoded.hold_appended`'s premise); rows read are
the Store's at their height (`Decoded.hold_read`'s). -/
def holdIndexRows (root : String) (height : Nat) (appended : Bool)
    (rows : List (List Bool × DurableIndex.Row)) : IO Unit :=
  -- One `alter` that moves the held map, so an insert updates it in place.
  decoded.modify fun all => all.alter root fun current => Decoded.hold current height appended rows

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
