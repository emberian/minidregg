/-
# Kernel.Contracts.Cuts — the six authority cuts

SHARED-CONTRACTS-20261003 §Authority, field for field:

    Observe(resource, projection, viewer, source dependencies, current law)
    Invoke(resource(s), command, actor, typed current guards, current law)
    Reserve(exact candidate, domain footprint, authorizing law, retained obligation)
    Install(committed candidate, protected preimage, exact effects, obligation)
    Release(exact result projection, current audience/device sources, then-current law)
    Retire(exact obligation, close/nullifier/anchor evidence, legal forgetting rule)

These are six distinct types. What each law permits is a `Governance`
interpretation of an exact `LawRef` (the law cell and its exact root), so a
cut carries the coordinate of the law it was decided under, never a flag.

Separations proved here:
* `observation_does_not_authorize_mutation` / `no_invoke_from_observe` — a
  signed observation does not authorize mutation: under a law that lets a
  viewer observe and lets SOMEONE mutate, no function from observations to
  invocations that keeps the actor is authorization-sound.
* `install_rechecks_today` / `historical_acceptance_does_not_bypass_today` —
  installation re-evaluates the invocation under TODAY's law: an invocation
  accepted under yesterday's law, with a held reservation, is refused after a
  role downgrade, and installs when the law is unchanged.
* `install_requires_reservation` — an install only consumes a held
  reservation's exact candidate and obligation.

The per-domain types refine into these cuts in `Kernel.Contracts.Refinements`.
-/
import Kernel.Contracts.Identities

namespace Minidregg.Kernel.Contracts

open Minidregg.Theory.TypedAuthorization (Digest SubjectId)

set_option autoImplicit false

/-! ## Shared field types -/

/-- A read dependency at an exact root (the shape of Mini's `ReadGuard`). -/
structure Guard where
  object : ObjectRef
  expectedRoot : Digest
  deriving DecidableEq, Repr

/-- The exact law a cut was decided under: the law cell and its exact root. -/
structure LawRef where
  cell : ObjectRef
  root : Digest
  deriving DecidableEq, Repr

/-- An exact projected value: its schema frame and its canonical bytes. -/
structure Projection where
  frame : List UInt8
  bytes : List UInt8
  deriving DecidableEq, Repr

/-- One exact effect (the shape of Mini's `DataWrite`). -/
structure Effect where
  object : ObjectRef
  expectedPre : Digest
  exactPost : Digest
  postBytes : List UInt8
  deriving DecidableEq, Repr

/-- A retained obligation: whose request, which single-use lineage, which domain. -/
structure Obligation where
  invocation : InvocationId
  lineage : Digest
  domain : Digest
  deriving DecidableEq, Repr

inductive RetireEvidence where
  | closed (acceptance : AcceptanceRef)
  | nullified (nullifier : Digest) (at_ : RevisionRef)
  | anchored (root : Digest) (at_ : RevisionRef)
  deriving DecidableEq, Repr

structure ForgettingRule where
  rule : Digest
  retainThrough : Nat
  deriving DecidableEq, Repr

/-! ## The six cuts -/

structure Observe where
  resource : ObjectRef
  projection : Projection
  viewer : SubjectId
  sources : List Guard
  law : LawRef
  deriving DecidableEq, Repr

structure Invoke where
  resources : List ObjectRef
  command : List UInt8
  actor : SubjectId
  guards : List Guard
  law : LawRef
  deriving DecidableEq, Repr

structure Reserve where
  candidate : List UInt8
  footprint : List ObjectRef
  law : LawRef
  obligation : Obligation
  deriving DecidableEq, Repr

structure Install where
  candidate : List UInt8
  preimage : List Guard
  effects : List Effect
  obligation : Obligation
  deriving DecidableEq, Repr

structure Release where
  projection : Projection
  audience : List Guard
  law : LawRef
  deriving DecidableEq, Repr

structure Retire where
  obligation : Obligation
  evidence : RetireEvidence
  forgetting : ForgettingRule
  deriving DecidableEq, Repr

/-! ## What a law permits -/

/-- The verdicts an exact law gives. Observation and mutation are separate
relations; neither is derived from the other. -/
structure Policy where
  mayObserve : ObjectRef → SubjectId → Projection → Bool
  mayInvoke : ObjectRef → SubjectId → List UInt8 → Bool

/-- How a deployment reads an exact law coordinate. -/
abbrev Governance := LawRef → Policy

def Observe.authorized (gov : Governance) (o : Observe) : Bool :=
  (gov o.law).mayObserve o.resource o.viewer o.projection

/-- An invocation is authorized under `law` when it names at least one resource
and the law lets its actor run its command on every one of them. -/
def Invoke.authorizedAt (gov : Governance) (law : LawRef) (i : Invoke) : Bool :=
  !i.resources.isEmpty && i.resources.all fun r => (gov law).mayInvoke r i.actor i.command

def Invoke.authorized (gov : Governance) (i : Invoke) : Bool := i.authorizedAt gov i.law

/-! ## A signed observation does not authorize mutation -/

def owner : SubjectId := ⟨1⟩
def reader : SubjectId := ⟨2⟩
def exampleObject : ObjectRef := ⟨⟨10⟩, ⟨1⟩, ⟨20⟩⟩
def lawCell : ObjectRef := ⟨⟨30⟩, ⟨1⟩, ⟨40⟩⟩
def yesterday : LawRef := ⟨lawCell, ⟨100⟩⟩
def today : LawRef := ⟨lawCell, ⟨101⟩⟩

/-- Everyone may observe; only `owner` may mutate. -/
def ownerOnly : Policy where
  mayObserve _ _ _ := true
  mayInvoke _ actor _ := decide (actor = owner)

def readerObservation : Observe :=
  ⟨exampleObject, ⟨[], []⟩, reader, [], yesterday⟩

theorem observation_does_not_authorize_mutation :
    ∃ gov : Governance, ∃ o : Observe,
      o.authorized gov = true ∧
      (∃ i : Invoke, i.authorized gov = true) ∧
      ∀ i : Invoke, i.actor = o.viewer → i.authorized gov = false := by
  refine ⟨fun _ => ownerOnly, readerObservation, rfl,
    ⟨⟨[exampleObject], [], owner, [], yesterday⟩, rfl⟩, ?_⟩
  intro i actor
  cases resources : i.resources with
  | nil => simp [Invoke.authorized, Invoke.authorizedAt, resources]
  | cons r rest =>
      simp [Invoke.authorized, Invoke.authorizedAt, resources, ownerOnly, actor,
        readerObservation, reader, owner]

/-- **No observation-to-invocation function is authorization-sound.** Any
`f : Observe → Invoke` that keeps the actor (the viewer becomes the actor) maps
some authorized observation to an unauthorized invocation, under a law in which
mutation is possible for someone. -/
theorem no_invoke_from_observe :
    ¬ ∃ f : Observe → Invoke, (∀ o, (f o).actor = o.viewer) ∧
      ∀ (gov : Governance) (o : Observe), o.authorized gov = true → (f o).authorized gov = true := by
  rintro ⟨f, keeps, sound⟩
  obtain ⟨gov, o, observed, _, refused⟩ := observation_does_not_authorize_mutation
  have := sound gov o observed
  rw [refused (f o) (keeps o)] at this
  cases this

/-! ## An accepted historical request does not bypass today's law -/

/-- Installation: the invocation is re-evaluated under `current` (not under the
law it was accepted under), and the install must consume a held reservation's
exact candidate and obligation. -/
def install? (gov : Governance) (current : LawRef) (held : List Reserve) (i : Invoke)
    (ins : Install) : Option Install :=
  if i.authorizedAt gov current &&
      held.any (fun r => decide (r.candidate = ins.candidate ∧ r.obligation = ins.obligation))
  then some ins else none

theorem install_rechecks_today {gov : Governance} {current : LawRef} {held : List Reserve}
    {i : Invoke} {ins out : Install} (installed : install? gov current held i ins = some out) :
    i.authorizedAt gov current = true ∧ out = ins := by
  unfold install? at installed
  split at installed
  · rename_i ok
    simp only [Bool.and_eq_true] at ok
    exact ⟨ok.1, (Option.some.inj installed).symm⟩
  · cases installed

theorem install_requires_reservation {gov : Governance} {current : LawRef} {held : List Reserve}
    {i : Invoke} {ins out : Install} (installed : install? gov current held i ins = some out) :
    ∃ r ∈ held, r.candidate = ins.candidate ∧ r.obligation = ins.obligation := by
  unfold install? at installed
  split at installed
  · rename_i ok
    simp only [Bool.and_eq_true] at ok
    obtain ⟨r, member, same⟩ := List.any_eq_true.mp ok.2
    exact ⟨r, member, of_decide_eq_true same⟩
  · cases installed

/-- Yesterday the owner could mutate; today's law (a role downgrade) refuses. -/
def downgrade : Governance := fun law =>
  if law = yesterday then ownerOnly else
    { mayObserve := fun _ _ _ => true, mayInvoke := fun _ _ _ => false }

def exampleInvocation : InvocationId := ⟨exampleSource, ⟨50⟩, ⟨51⟩⟩
def exampleObligation : Obligation := ⟨exampleInvocation, ⟨60⟩, ⟨1⟩⟩
def exampleInvoke : Invoke := ⟨[exampleObject], [7], owner, [], yesterday⟩
def exampleInstall : Install := ⟨[7], [], [], exampleObligation⟩
def exampleReserve : Reserve := ⟨[7], [exampleObject], yesterday, exampleObligation⟩

theorem historical_acceptance_does_not_bypass_today :
    exampleInvoke.law = yesterday ∧
    exampleInvoke.authorized downgrade = true ∧
    (∃ r ∈ [exampleReserve], r.candidate = exampleInstall.candidate ∧
      r.obligation = exampleInstall.obligation) ∧
    install? downgrade today [exampleReserve] exampleInvoke exampleInstall = none ∧
    install? downgrade yesterday [exampleReserve] exampleInvoke exampleInstall = some exampleInstall := by
  refine ⟨rfl, by decide, ⟨exampleReserve, List.mem_singleton_self _, rfl, rfl⟩, by decide, by decide⟩

#assert_axioms observation_does_not_authorize_mutation
#assert_axioms no_invoke_from_observe
#assert_axioms install_rechecks_today
#assert_axioms install_requires_reservation
#assert_axioms historical_acceptance_does_not_bypass_today

end Minidregg.Kernel.Contracts
