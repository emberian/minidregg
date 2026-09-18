/-
# Theory.PolicyInstall -- source succession and the pre-authorization candidate

The statement is independent of a predicate compiler or byte representation.
A policy source has complete version/domain/semantics metadata. An initial
source starts at epoch zero without a predecessor; an update advances exactly
one epoch and names the current content address.

Policy evaluation consumes a candidate already derived from one canonical
pre-cell and one semantic family declaration. That candidate contains mode
evidence and the validated patch, but no authorization. Authorization is
added only after evaluation; the resulting accepted effect installs precisely
the candidate that was evaluated.
-/
import Theory.AcceptedCellEffect

namespace Minidregg.Theory.PolicyInstall

open CellState
open IndexedProgram
open TypedAuthorization

set_option autoImplicit false

structure Source (Body : Type) where
  policyId : PolicyId
  version : Epoch
  domain : Digest
  semantics : Digest
  previous : Option Digest
  body : Body
  deriving DecidableEq, Repr

structure Head where
  version : Epoch
  address : Digest
  deriving DecidableEq, Repr

def Successor {Body : Type} (current : Option Head) (source : Source Body) : Prop :=
  match current with
  | none => source.version = 0 ∧ source.previous = none
  | some head => source.version = head.version + 1 ∧ source.previous = some head.address

instance successorDecidable {Body : Type} (current : Option Head) (source : Source Body) :
    Decidable (Successor current source) := by
  unfold Successor
  split <;> infer_instance

def checkSuccessor {Body : Type} (current : Option Head) (source : Source Body) : Bool :=
  decide (Successor current source)

theorem checkSuccessor_iff {Body : Type} (current : Option Head) (source : Source Body) :
    checkSuccessor current source = true ↔ Successor current source := by
  simp [checkSuccessor]

theorem current_version_cannot_install {Body : Type} (current : Head) (source : Source Body)
    (same : source.version = current.version) : checkSuccessor (some current) source = false := by
  simp [checkSuccessor, Successor, same]

theorem wrong_predecessor_cannot_install {Body : Type}
    (current : Head) (source : Source Body)
    (wrong : source.previous ≠ some current.address) :
    checkSuccessor (some current) source = false := by
  simp [checkSuccessor, Successor, wrong]

theorem successor_inhabited {Body : Type} (source : Source Body) (current : Head) :
    checkSuccessor (some current)
      { source with version := current.version + 1, previous := some current.address } = true := by
  simp [checkSuccessor, Successor]

universe u v w x y z

/-- A candidate is prepared before policy authorization. In particular the
post-state cannot be an unconstrained witness supplied beside the request. -/
structure Candidate
    {S : Schema.{u, v, w, x}} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : Materializer S Digest} {Nullifier : Type y}
    (family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier)
    (pre : Materialized M) (declaration : family.Declaration)
    (outcome : family.Outcome declaration) where
  modeEvidence : family.ModeEvidence declaration outcome
  validated : ValidatedPatch M pre (family.patch declaration outcome)

namespace Candidate

variable
    {S : Schema.{u, v, w, x}} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    {pre : Materialized M} {declaration : family.Declaration}
    {outcome : family.Outcome declaration}

def post (candidate : Candidate family pre declaration outcome) : Materialized M :=
  candidate.validated.apply

/-- The existing accepted-effect token is the only admission result. Its
validated patch is exactly the candidate evaluated by the policy consumer. -/
def accept (candidate : Candidate family pre declaration outcome)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {request : Request kind} (authorization : Authorized portal authState request)
    (preRoot : request.preStateRoot = pre.root)
    (effects : request.effectsDigest = family.effectDigest declaration)
    (disclosure : DisclosureDecision (family.Release declaration outcome)
      (family.DeclassificationAuthority declaration outcome)
      (family.ReleaseAuthorization declaration outcome))
    (allowed : family.DisclosureAllowed declaration outcome disclosure) :
    AcceptedCellEffect (portal := portal) (authState := authState)
      family request pre declaration outcome where
  authorization := authorization
  effectsDigestBound := effects
  preRootBound := preRoot
  modeEvidence := candidate.modeEvidence
  validated := candidate.validated
  disclosure := disclosure
  disclosureAllowed := allowed

theorem accepted_post_is_evaluated_post (candidate : Candidate family pre declaration outcome)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {request : Request kind} (authorization : Authorized portal authState request)
    (preRoot : request.preStateRoot = pre.root)
    (effects : request.effectsDigest = family.effectDigest declaration)
    (disclosure : DisclosureDecision (family.Release declaration outcome)
      (family.DeclassificationAuthority declaration outcome)
      (family.ReleaseAuthorization declaration outcome))
    (allowed : family.DisclosureAllowed declaration outcome disclosure) :
    (candidate.accept authorization preRoot effects disclosure allowed).prepared.post =
      candidate.post := rfl

end Candidate
end Minidregg.Theory.PolicyInstall
