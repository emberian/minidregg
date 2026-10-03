/- Runtime reordering preserves source observations; admission/liveness still
requires the actual reordered Book.check because declaration indices matter. -/
import Compiler.ObjectiveBendLinker
import Theory.BendBookTransport
import Theory.AssertAxioms
namespace Minidregg.Compiler.ObjectiveBendLinkerRefinement
open Minidregg.Theory.BendTT
open ObjectiveBendComposition ObjectiveBendElaboration ObjectiveBendLinker
set_option autoImplicit false
variable {helpers : Book} {layers : List Spec}

theorem candidate_exact (linked : Linked helpers layers) (d : Def)
    (present : d ∈ candidate helpers layers) : Book.get linked.core.book d.k = some d := by
  rcases List.mem_append.mp present with helper | method
  · exact linked.helperEntries d helper
  · rcases List.mem_flatMap.mp method with ⟨i, _, method⟩
    rcases List.mem_map.mp method with ⟨p, member, identity⟩
    subst d
    exact linked.entries i p member

theorem lookup_equivalent (linked : Linked helpers layers) :
    Minidregg.Theory.BendBookTransport.LookupEquivalent linked.core.book (candidate helpers layers) := by
  intro name
  cases found : Book.get (candidate helpers layers) name with
  | some d =>
    have present : d ∈ candidate helpers layers := List.mem_of_find?_eq_some found
    have named : d.k = name := by simpa using List.find?_some found
    simpa [named] using candidate_exact linked d present
  | none =>
    cases coreFound : Book.get linked.core.book name with
    | none => rfl
    | some d =>
      have inCore : d ∈ linked.core.book := List.mem_of_find?_eq_some coreFound
      have inCandidate : d ∈ candidate helpers layers := (linked_definitions linked).mem_iff.mp inCore
      have absent := List.find?_eq_none.mp found d inCandidate
      exact False.elim (absent (List.find?_some coreFound))

theorem eval_retained (linked : Linked helpers layers)
    (before after : Minidregg.Theory.BendTT.Term) :
    Eval linked.core.book before after ↔ Eval (candidate helpers layers) before after :=
  Minidregg.Theory.BendBookTransport.eval_iff (lookup_equivalent linked)

theorem trace_retained (linked : Linked helpers layers) (count : Nat)
    (before after : Minidregg.Theory.BendTT.Term) :
    Minidregg.Theory.BendLiveMachine.Trace linked.core.book count before after ↔
      Minidregg.Theory.BendLiveMachine.Trace (candidate helpers layers) count before after :=
  Minidregg.Theory.BendBookTransport.trace_iff (lookup_equivalent linked)

#assert_axioms trace_retained
#assert_axioms candidate_exact
#assert_axioms lookup_equivalent
#assert_axioms eval_retained
end Minidregg.Compiler.ObjectiveBendLinkerRefinement
