import Kernel.GenericSimplex
import Theory.AssertAxioms

namespace Minidregg.Compiler.GenericSimplexPending
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false

/-- Work is derived from the durable protocol journal, so a restart does not
forget a received proposal merely because it never became locally valid. -/
def observedBlocks (s : State) : List Block :=
  s.views.flatMap fun v => v.proposal.toList ++ v.received.filterMap Message.value

/-- Every application-bearing sourcePrefix is checked at its original exact ancestry.
Protocol-only empty blocks never introduce application authority. -/
def applicationPrefixes (block : Block) : List Block :=
  let history := applicationHistory block
  (List.range history.length).map (fun i => history.take (i + 1))

/-- Application prefixes requested by the given observed blocks and by this
replica's own offers over its current best parent. -/
def requestedFrom (s : State) (observed : List Block) : List Block :=
  let localOffers := s.offers.map (fun payload => bestParent s ++ [payload])
  ((observed ++ localOffers).flatMap applicationPrefixes).eraseDups

def requestedPrefixes (s : State) : List Block := requestedFrom s (observedBlocks s)

/-- Native controller bookkeeping, not protocol agreement or a source grant.
On restart rebuild from the durable engine state. Forgetting a negative cache
causes another check; it cannot turn an unvalidated sourcePrefix into checked input. -/
structure Queue where
  pending : List Block := []
  rejected : List Block := []
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Newly observed work is appended, never inserted ahead of retained work.
Missing-dependency attempts rotate to the tail. Under fair funded service and
finitely many arrivals per step, later traffic cannot continually overtake a
particular queued sourcePrefix. Infinite restart and exhausted funding need separate
progress assumptions; this scheduler does not manufacture those resources. -/
def appendFresh (old incoming : List Block) : List Block :=
  old ++ (incoming.filter fun b => !old.contains b).eraseDups

/-- Not yet checked and not already rejected. -/
def wanted (s : State) (queue : Queue) (b : Block) : Bool :=
  !s.checked.any (fun checked => applicationHistory checked == b) && !queue.rejected.contains b

/-- Discovery over the given observed blocks plus this replica's own offers.
The retained queue is refiltered, never reordered. -/
def discoverFrom (s : State) (observed : List Block) (queue : Queue) : Queue :=
  let old := queue.pending.filter (wanted s queue)
  let incoming := (requestedFrom s observed).filter (wanted s queue)
  { queue with pending := appendFresh old incoming }

/-- Full discovery: every block this replica has ever observed. Run once when a
participant opens; afterwards each acknowledged input contributes only the
blocks it carries (`discoverFrom`). Rescanning every observed block on every
input and every service slice made each idle replica's per-input cost grow with
its whole history (measured on the 00f711 evidence copy: about 1 s of every
service slice). -/
def discover (s : State) (queue : Queue) : Queue := discoverFrom s (observedBlocks s) queue

/-- Removing work is not accepting it. Only the source receiver's opaque
historical-sourcePrefix validation capability may cause native Input.checked.
Every observed block was discovered when its input was journaled, so a slice
refilters the retained queue and re-derives only this replica's own offers. -/
def take (s : State) (queue : Queue) : Option (Block × Queue) :=
  let queue := discoverFrom s [] queue
  match queue.pending with
  | [] => none
  | sourcePrefix :: rest => some (sourcePrefix,{queue with pending := rest})

def retry (queue : Queue) (sourcePrefix : Block) : Queue :=
  { queue with pending := addUnique queue.pending sourcePrefix }

def reject (queue : Queue) (sourcePrefix : Block) : Queue :=
  { queue with rejected := addUnique queue.rejected sourcePrefix }

/-- The exact finite old queue remains ahead of every newly discovered sourcePrefix. -/
theorem appendFresh_retains_order (old incoming : List Block) :
    ∃ added, appendFresh old incoming = old ++ added :=
  ⟨_,rfl⟩

/-- Validation discovery cannot change any consensus state or grant checked
authority: it only constructs the separate queue. -/
theorem retry_appends (queue : Queue) (sourcePrefix : Block)
    (absent : queue.pending.contains sourcePrefix = false) :
    (retry queue sourcePrefix).pending = queue.pending ++ [sourcePrefix] := by
  simp only [retry,addUnique,absent, Bool.false_eq_true, ↓reduceIte]

#assert_axioms appendFresh_retains_order
#assert_axioms retry_appends
end Minidregg.Compiler.GenericSimplexPending
