import Kernel.GenericSimplex
import Theory.AssertAxioms

namespace Minidregg.Compiler.GenericSimplexPending
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false

/-- Work is derived from the durable protocol journal, so a restart does not
forget a received proposal merely because it never became locally valid. -/
def observedBlocks (s : State) : List Block :=
  s.views.flatMap fun v => v.proposal.toList ++ v.received.filterMap Message.value

/-- Every application-bearing prefix is checked at its original exact ancestry.
Protocol-only empty blocks never introduce application authority. -/
def applicationPrefixes (block : Block) : List Block :=
  let history := applicationHistory block
  (List.range history.length).map (fun i => history.take (i + 1))

def requestedPrefixes (s : State) : List Block :=
  let proposed := observedBlocks s
  let localOffers := s.offers.map (fun payload => bestParent s ++ [payload])
  ((proposed ++ localOffers).flatMap applicationPrefixes).eraseDups

/-- Native controller bookkeeping, not protocol agreement or a source grant.
On restart rebuild from the durable engine state. Forgetting a negative cache
causes another check; it cannot turn an unvalidated prefix into checked input. -/
structure Queue where
  pending : List Block := []
  rejected : List Block := []
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Newly observed work is appended, never inserted ahead of retained work.
Missing-dependency attempts rotate to the tail. Under fair funded service and
finitely many arrivals per step, later traffic cannot continually overtake a
particular queued prefix. Infinite restart and exhausted funding need separate
progress assumptions; this scheduler does not manufacture those resources. -/
def appendFresh (old incoming : List Block) : List Block :=
  old ++ (incoming.filter fun b => !old.contains b).eraseDups

def discover (s : State) (queue : Queue) : Queue :=
  let wanted := fun b => !s.checked.any (fun checked => applicationHistory checked == b) && !queue.rejected.contains b
  let old := queue.pending.filter wanted
  let incoming := (requestedPrefixes s).filter wanted
  { queue with pending := appendFresh old incoming }

/-- Removing work is not accepting it. Only the source receiver's opaque
historical-prefix validation capability may cause native Input.checked. -/
def take (s : State) (queue : Queue) : Option (Block × Queue) :=
  let queue := discover s queue
  match queue.pending with
  | [] => none
  | prefix :: rest => some (prefix,{queue with pending := rest})

def retry (queue : Queue) (prefix : Block) : Queue :=
  { queue with pending := addUnique queue.pending prefix }

def reject (queue : Queue) (prefix : Block) : Queue :=
  { queue with rejected := addUnique queue.rejected prefix }

/-- The exact finite old queue remains ahead of every newly discovered prefix. -/
theorem appendFresh_retains_order (old incoming : List Block) :
    ∃ added, appendFresh old incoming = old ++ added :=
  ⟨_,rfl⟩

/-- Validation discovery cannot change any consensus state or grant checked
authority: it only constructs the separate queue. -/
theorem retry_appends (queue : Queue) (prefix : Block)
    (absent : queue.pending.contains prefix = false) :
    (retry queue prefix).pending = queue.pending ++ [prefix] := by
  simp [retry,addUnique,absent]

#assert_axioms appendFresh_retains_order
#assert_axioms retry_appends
end Minidregg.Compiler.GenericSimplexPending
