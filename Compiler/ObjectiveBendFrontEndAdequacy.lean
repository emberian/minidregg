/- What the Lean front end's acceptance buys, stated on the ELABORATOR's term.

`ObjectiveBendFrontEnd.Accepted l` is the front end checking its own output: the
packet it rendered decodes (with the checker's decoder) to exactly the erasure of
the elaborator's annotated term (`packetTerm`, proved by
`ObjectiveBendTermWire.decode_json`), and the proof-producing checker accepted it
closed. Composed with the Core4 metatheory this gives, for every program the front
end accepts:

* `accepted_typed`: the erased elaborator term is closed and has the checker's
  typing derivation;
* `accepted_never_refused`: the bounded demand machine never refuses it, at any
  tick, heap or stack budget (it finishes, yields, suspends or blackholes);
* `accepted_execution_semantics`: a finished bounded run of it extracts THE deep
  source evaluation of that term (`deepEvaluates_unique`): a Data deep-evaluates
  the term exactly when it is the extracted Data, under every policy and budget.

`accept_inhabited` exhibits a real `.obend` program the front end accepts, so the
premises are inhabited. What is NOT stated (no surface semantics exists): that the
Core4 term means what the surface program means. The publication/receiver binding
of the front-end identity is `Kernel.ObjectiveBendAdmissionSemantics.admitted_front_end`. -/
import Compiler.ObjectiveBendPublication
import Theory.ObjectiveBendDemandPreservation
import Theory.ObjectiveBendDemandDataSoundness
import Theory.ObjectiveBendDemandTyping
import Theory.AssertCompiled
namespace Minidregg.Compiler.ObjectiveBendFrontEndAdequacy
open Lean
open Minidregg.Compiler.ObjectiveBendFrontEnd
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandDataSoundness
set_option autoImplicit false

theorem accepted_typed (l : Lowering) (a : Accepted l) :
    l.term.erase = .ok a.erased ∧
    PartialTyping a.source.assumptions [] a.erased a.typed.type a.typed.uses ∧
    Minidregg.Theory.ObjectiveBendDemandInvariant.Scoped 0 a.erased := by
  have derivation := a.typed.derivation
  have term : a.source.erase = a.erased := by rw [a.sourceExact]; rfl
  rw [term] at derivation
  exact ⟨a.erasure, derivation, Minidregg.Theory.ObjectiveBendDemandTyping.source_scoped derivation⟩

theorem accepted_never_refused (l : Lowering) (a : Accepted l) (limits : Limits) (ticks : Nat)
    (reason : Refusal) (retained : State) :
    runBounded limits ticks (initial a.erased) ≠ .refused reason retained := by
  have := Minidregg.Theory.ObjectiveBendDemandPreservation.check_runBounded_no_refusal
    a.source a.packet.fuel a.typed a.checkedExact limits ticks reason retained
  have term : a.source.erase = a.erased := by rw [a.sourceExact]; rfl
  rwa [term] at this

theorem accepted_execution_semantics (l : Lowering) (a : Accepted l) {policy : State → Bool}
    {limits : Limits} {budget : Minidregg.Theory.ObjectiveBendDemandData.Budget}
    (execution : Minidregg.Theory.ObjectiveBendDemandData.ExecutionWith policy limits budget a.erased) :
    runBounded limits budget.ticks (initial a.erased) = .finished execution.value execution.state ∧
      ∀ data, DeepEvaluates a.erased data ↔ data = execution.extraction.result.value :=
  execution_source_semantics (accepted_typed l a).2.2 execution

/-! ## Inhabitant: a surface program the front end accepts -/

/-- Even/odd by open recursion over two specifications, tied by `fix`, and a `let`
(surface `.obend`). -/
def example_source : String :=
  "edition ObjectiveBend 1\n" ++
  "record Parity:\n  even(n: Nat) -> Bool\n  odd(n: Nat) -> Bool\n" ++
  "spec Even for Parity:\n  requires odd(n: Nat) -> Bool\n  def even(n: Nat) -> Bool:\n" ++
  "    match n:\n      case 0n: true\n      case 1n+p: self.odd(p)\n" ++
  "spec Odd for Parity:\n  requires even(n: Nat) -> Bool\n  def odd(n: Nat) -> Bool:\n" ++
  "    match n:\n      case 0n: false\n      case 1n+p: self.even(p)\n" ++
  "def ten(seed: Parity) -> Bool:\n  let parity = fix(compose(Even, Odd), seed)\n  parity.even(10n)\n"

def example_module : SourceModule := ⟨"Example", example_source, Sha256.hexString example_source, []⟩

def example_lowering : Except Diagnostic Lowering :=
  ObjectiveBendFrontEnd.lower [example_module] 0 "ten" (Json.arr #[]) (Json.arr #[])
    (Json.mkObj [("heap", toJson "100000"), ("stack", toJson "100000"), ("ticks", toJson "100000")]) "definition"

/-- The front end accepts the example: its packet decodes to the elaborator's erased term
and the checker returns a derivation. -/
theorem accept_inhabited :
    (match example_lowering with
      | .ok l => (ObjectiveBendFrontEnd.accept l).toBool
      | .error _ => false) = true := by
  native_decide
#assert_compiled accept_inhabited

/-- The example as a one-module source package naming this front end. -/
def example_package : ObjectiveSourcePackage.Package :=
  ⟨ObjectiveBendFrontEndIdentity.identity, [⟨"Example", example_source.toUTF8.toList, []⟩], 0, "ten"⟩

/-- A receiver's replay token is inhabited: replaying the example package against the core it
publishes succeeds (`ObjectiveBendPublication.Replayed`, the premise of
`Kernel.ObjectiveBendAdmissionSemantics.admitted_front_end` and of the activity kernel's
`Program.runs_front_end_output`). -/
theorem replay_inhabited :
    (ObjectiveBendPublication.replayAccept example_package
      ((ObjectiveBendPublication.publishedCore example_package).toOption.getD [])
      ((ObjectiveBendPublication.publishedLaws example_package).toOption.getD []) 16384).toBool = true := by
  native_decide
#assert_compiled replay_inhabited


#assert_axioms accepted_typed
#assert_axioms accepted_never_refused
#assert_axioms accepted_execution_semantics
end Minidregg.Compiler.ObjectiveBendFrontEndAdequacy
