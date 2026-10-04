/- Canonical physical source guards for the shared authenticated law closure. -/
import Compiler.CanonicalCellRegistry
import Compiler.ComposedPolicyAdmission
import Compiler.WorldKindLawDependencies

namespace Minidregg.Compiler.PhysicalLawResolution

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.LawComposition
open Minidregg.Theory.CellRegistry
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.PolicyComponentResolution
open Minidregg.Kernel.CanonicalPolicyRegistry

set_option autoImplicit false

def payloadStore (snapshot : Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry) : PayloadStore :=
  ⟨CanonicalCellRegistry.fetchPolicySource snapshot.domain directory⟩

/-- Includes every actual historical predecessor read, not only the pin and
head. Parentage and head selection also require the receiver's authority guard. -/
def addresses {snapshot : Snapshot} {store : PayloadStore} {semantics : Digest}
    {refs : List PolicyRef} (graph : LoadedRoots snapshot store semantics refs) : List Digest :=
  (graph.sources.flatMap fun loaded =>
    loaded.source.history.records.map CommittedPolicy.address).eraseDups

def loadGuards (snapshot : Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry)
    (addresses : List Digest) : Option (List (Nat × Digest)) :=
  addresses.mapM fun address => do
    let source ← CanonicalCellRegistry.loadPolicySource snapshot.domain directory address
    pure source.readGuard

structure GuardedRoots (snapshot : Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry)
    (semantics : Digest) (refs : List PolicyRef) where
  graph : LoadedRoots snapshot (payloadStore snapshot directory) semantics refs
  sourceGuards : List (Nat × Digest)
  guardsExact : loadGuards snapshot directory (addresses graph) = some sourceGuards

def loadRoots (snapshot : Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry)
    (semantics : Digest) (refs : List PolicyRef) (budget : Nat) :
    Option (GuardedRoots snapshot directory semantics refs) := do
  let graph ← (PolicyComponentResolution.loadRoots snapshot (payloadStore snapshot directory)
    semantics refs budget).toOption
  match exact : loadGuards snapshot directory (addresses graph) with
  | none => none
  | some guards => pure ⟨graph, guards, exact⟩

def loadTarget (snapshot : Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry)
    (semantics : Digest) (target budget : Nat) (additional : List PolicyRef := []) :
    Option (GuardedRoots snapshot directory semantics (targetRoots snapshot target additional)) :=
  loadRoots snapshot directory semantics (targetRoots snapshot target additional) budget

/-- Source-owned resource bound shared by all native composition consumers.
Budget exhaustion refuses; it never truncates a restriction conjunction. -/
def resolutionBudget : Nat := 4096

def config {F : Type} [Field F] [DecidableEq F]
    (profile : PolicyCompilerProfile F) (snapshot : Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry) (base : Portal)
    (step : PolicyStepContext) (target : Nat) (additional : List PolicyRef := []) :
    ComposedPolicyAdmission.Config F where
  snapshot := snapshot
  store := payloadStore snapshot directory
  base := base
  profile := profile
  step := step
  target := target
  additional := additional
  resolutionBudget := resolutionBudget

/-- The configuration that judges `target`'s committed law on `step` at one loaded snapshot, its
structural (world-kind) restrictions read from the same directory. The one copy: the DRC's legs
(`DeclaredResourceController.policyConfigFromStep`) and the Receiver's law judgement
(`Kernel.Receiving.Laws.physical`) both build it here. -/
def targetConfig {F : Type} [Field F] [DecidableEq F]
    (deployment : CanonicalCellRegistry.Deployment) (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (directory : Directory Nat CanonicalCellRegistry.registry) (base : Portal)
    (step : PolicyStepContext) (target : Nat) : ComposedPolicyAdmission.Config F :=
  config profile snapshot directory base step target
    ((WorldKindLawDependencies.loadTarget deployment directory target).map (·.additional) |>.getD [])

/-- One law judgement: the resolved committed law of a configuration, with the compiler's verdicts
on its step -- every input the law reads is in range, and the field cast of those inputs is
injective. A false verdict REFUSES (`policyInputRange`, `policyCastAlias`); it never degrades to a
false predicate or a skipped law. -/
structure Judged {F : Type} [Field F] [DecidableEq F] (config : ComposedPolicyAdmission.Config F) where
  law : ComposedPolicyAdmission.PreparedLaw config
  inRange : Bool
  castsInjective : Bool

/-- The judgement of a configuration: `config.resolve?`, then `inputsInRange` and `castInjOn` on its
own step. The one sequence: the DRC's `authorizeLeg` and the Receiver's `Laws.physical` run it. -/
def judge {F : Type} [Field F] [DecidableEq F] (config : ComposedPolicyAdmission.Config F) :
    Option (Judged config) := do
  let law ← config.resolve?
  pure ⟨law,
    inputsInRange config.profile.compiler law.predicate config.step.oldState config.step.newState,
    decide (castInjOn F (intsOf law.predicate config.step.oldState config.step.newState))⟩

/-- The judgement is the resolution, with its two verdicts read on the resolved law. -/
theorem judge_some_iff {F : Type} [Field F] [DecidableEq F] (config : ComposedPolicyAdmission.Config F)
    (judged : Judged config) :
    judge config = some judged ↔
      config.resolve? = some judged.law ∧
      judged.inRange = inputsInRange config.profile.compiler judged.law.predicate
        config.step.oldState config.step.newState ∧
      judged.castsInjective =
        decide (castInjOn F (intsOf judged.law.predicate config.step.oldState config.step.newState)) := by
  unfold judge
  cases resolved : config.resolve? with
  | none => simp
  | some found =>
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨rfl, rfl, rfl⟩
      · obtain ⟨law, inRange, casts⟩ := judged
        rintro ⟨lawEq, rangeEq, castEq⟩
        simp only at lawEq rangeEq castEq
        subst lawEq
        rw [rangeEq, castEq]

/-- **The judgement does not read the base portal**: two target configurations that differ only
in the capability portal they carry judge the same law with the same verdicts. So the DRC's legs
(which carry the operation's capability portal) and the Receiver (which carries none it uses)
judge one law. -/
theorem judge_portal_irrelevant {F : Type} [Field F] [DecidableEq F]
    (deployment : CanonicalCellRegistry.Deployment) (profile : PolicyCompilerProfile F)
    (snapshot : Snapshot) (directory : Directory Nat CanonicalCellRegistry.registry) (left right : Portal)
    (step : PolicyStepContext) (target : Nat) :
    (judge (targetConfig deployment profile snapshot directory left step target)).map
        (fun judged => (judged.law.predicate, judged.inRange, judged.castsInjective)) =
      (judge (targetConfig deployment profile snapshot directory right step target)).map
        (fun judged => (judged.law.predicate, judged.inRange, judged.castsInjective)) := by
  simp only [judge, ComposedPolicyAdmission.Config.resolve?, targetConfig, config,
    ComposedPolicyAdmission.PreparedLaw.predicate]
  repeat' split
  all_goals rfl

def readGuards (snapshot : Snapshot)
    (directory : Directory Nat CanonicalCellRegistry.registry)
    (semantics : Digest) (target : Nat) (additional : List PolicyRef := []) :
    Option (List (Nat × Digest)) :=
  (loadTarget snapshot directory semantics target resolutionBudget additional).map
    GuardedRoots.sourceGuards

#assert_axioms judge_some_iff
#assert_axioms judge_portal_irrelevant

end Minidregg.Compiler.PhysicalLawResolution
