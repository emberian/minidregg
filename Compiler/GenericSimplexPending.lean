module

public import Kernel.GenericSimplexRelative
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

namespace Minidregg.Compiler.GenericSimplexPending
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexRelative
set_option autoImplicit false

/-- Source records to check: `records`, starting at application height `height`. The
history they denote is the committed records below `height` followed by `records`. -/
structure Work where
  height : Nat
  records : Block
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Work is derived from the durable protocol journal, so a restart does not
forget a received proposal merely because it never became locally valid. The blocks are the
replica's own: the payloads above its committed height. -/
def observedBlocks (r : Replica) : List Block :=
  r.core.views.flatMap fun v => v.proposal.toList ++ v.received.filterMap Message.value

/-- Every application-bearing sourcePrefix is checked at its original exact ancestry.
Protocol-only empty blocks never introduce application authority. -/
def applicationPrefixes (block : Block) : List Block :=
  let history := applicationHistory block
  (List.range history.length).map (fun i => history.take (i + 1))

/-- Application prefixes requested by the given observed blocks and by this
replica's own offers over its current best parent, as work above its committed records. -/
def requestedFrom (r : Replica) (observed : List Block) : List Work :=
  let localOffers := r.core.offers.map (fun payload => bestParent r.core ++ [payload])
  ((observed ++ localOffers).flatMap applicationPrefixes).eraseDups.map fun records => ⟨r.records,records⟩

/-- Native controller bookkeeping, not protocol agreement or a source grant.
On restart rebuild from the durable engine state. Forgetting a negative cache
causes another check; it cannot turn an unvalidated sourcePrefix into checked input. -/
structure Queue where
  pending : List Work := []
  rejected : List Work := []
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Newly observed work is appended, never inserted ahead of retained work.
Missing-dependency attempts rotate to the tail. Under fair funded service and
finitely many arrivals per step, later traffic cannot continually overtake a
particular queued sourcePrefix. Infinite restart and exhausted funding need separate
progress assumptions; this scheduler does not manufacture those resources. -/
def appendFresh (old incoming : List Work) : List Work :=
  old ++ (incoming.filter fun b => !old.contains b).eraseDups

/-- Still work: it reaches above the committed records, is not yet checked and not already
rejected. Work at or below the committed records is settled by the commit. -/
def wanted (r : Replica) (queue : Queue) (w : Work) : Bool :=
  match above w.height r.records w.records with
  | some run => !validBlock r.core run && !queue.rejected.contains w
  | none => false

/-- Discovery over the given observed blocks and named work (every prefix of it) plus this
replica's own offers. The retained queue is refiltered, never reordered. -/
def discoverFrom (r : Replica) (observed : List Block) (queue : Queue) (named : List Work := []) : Queue :=
  let old := queue.pending.filter (wanted r queue)
  let prefixes := named.flatMap fun work =>
    (applicationPrefixes work.records).map fun records => (⟨work.height,records⟩ : Work)
  let incoming := (requestedFrom r observed ++ prefixes).filter (wanted r queue)
  { queue with pending := appendFresh old incoming }

/-- Full discovery: every block this replica holds. Run once when a participant opens;
afterwards each acknowledged input contributes only the blocks it carries
(`discoverFrom`). The replica holds blocks only for the views above its floor, so this is
bounded by its live state. -/
def discover (r : Replica) (queue : Queue) : Queue := discoverFrom r (observedBlocks r) queue

/-- Removing work is not accepting it. Only the source receiver's opaque
historical-sourcePrefix validation capability may cause a native checked input.
Every observed block was discovered when its input was journaled, so a slice
refilters the retained queue and re-derives only this replica's own offers. -/
def take (r : Replica) (queue : Queue) : Option (Work × Queue) :=
  let queue := discoverFrom r [] queue
  match queue.pending with
  | [] => none
  | work :: rest => some (work,{queue with pending := rest})

def retry (queue : Queue) (work : Work) : Queue :=
  { queue with pending := addUnique queue.pending work }

def reject (queue : Queue) (work : Work) : Queue :=
  { queue with rejected := addUnique queue.rejected work }

/-- The exact finite old queue remains ahead of every newly discovered sourcePrefix. -/
theorem appendFresh_retains_order (old incoming : List Work) :
    ∃ added, appendFresh old incoming = old ++ added :=
  ⟨_,rfl⟩

/-- Validation discovery cannot change any consensus state or grant checked
authority: it only constructs the separate queue. -/
theorem retry_appends (queue : Queue) (work : Work)
    (absent : queue.pending.contains work = false) :
    (retry queue work).pending = queue.pending ++ [work] := by
  simp only [retry,addUnique,absent, Bool.false_eq_true, ↓reduceIte]

#assert_axioms appendFresh_retains_order
#assert_axioms retry_appends
end Minidregg.Compiler.GenericSimplexPending
