/-
# Theory.TypedAuthorizationWitness -- the authority layer has subjects

`Theory/TypedAuthorization.lean` defines `Portal`, `AuthState`, `Evidence`, and
`Authorized`, proves a careful set of negative theorems about them, and never
exhibits an `Authorized`.  The negative theorems are the valuable half and they
survive untouched; what was missing is the other half, and without it
"`Authorized` is the sole request-indexed authority" is a claim about a type
nobody had shown to be inhabited.

This module builds a portal, an authority state, and a request, and produces
an `Authorized`.  Then it does the part that makes the witness worth having:
it shows the same construction FAILS, as a refutation rather than an
unproved gap, when the policy gate rejects and when the request quotes the
wrong policy epoch.

The permissive portal here verifies everything.  That is the correct shape for
an inhabitation witness and the wrong shape for a security claim, and the
teeth below are what keep the difference visible: authority does not follow
from evidence alone, and a permissive portal is not a permissive `Authorized`.
-/
import Theory.TypedAuthorization

namespace Minidregg.Theory.TypedAuthorizationWitness

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Built parameters -/

/-- A portal that accepts every witness.  Inhabitation only: this is exactly
the portal a security claim may not use. -/
def permissivePortal : Portal where
  SignatureWitness := Unit
  ProofWitness := Unit
  CapabilityCommitmentWitness := Unit
  MembershipWitness := Unit
  IssuerWitness := Unit
  NonRevocationWitness := Unit
  PolicyWitness := Unit
  verifySignature := fun _ _ => true
  verifyProof := fun _ _ => true
  verifyCapabilityCommitment := fun _ _ _ => true
  verifyMembership := fun _ _ _ => true
  verifyIssuer := fun _ _ _ _ => true
  verifyNonRevocation := fun _ _ _ => true
  verifyPolicy := fun _ _ => true

/-- The same portal with the one common final gate closed.  Every evidence
mode still verifies. -/
def policyClosedPortal : Portal :=
  { permissivePortal with verifyPolicy := fun _ _ => false }

/-- A blank authority state: nothing revoked, every epoch zero. -/
def authState : AuthState where
  capabilityRoot := ⟨0⟩
  revocationRoot := ⟨0⟩
  revoked := ∅
  issuerEpoch := fun _ => 0
  policyEpoch := fun _ => 0
  subjectKeyEpoch := fun _ => 0

/-- One complete request, quoting the state's policy epoch exactly. -/
def request : Request .object where
  domain := ⟨1⟩
  semantics := ⟨2⟩
  federation := ⟨3⟩
  subject := ⟨4⟩
  subjectKeyEpoch := 0
  target := ⟨5⟩
  verb := .mutateObject
  argsDigest := ⟨6⟩
  effectsDigest := ⟨7⟩
  nonce := 8
  height := 9
  preStateRoot := ⟨0⟩
  policyId := ⟨10⟩
  policyEpoch := 0
  cost := 11

/-- A second complete request, on a different target, quoting pre-state root
`⟨1⟩` -- the second cell of a joint turn. -/
def requestTrue : Request .object :=
  { request with
    target := ⟨6⟩
    argsDigest := ⟨16⟩
    effectsDigest := ⟨17⟩
    nonce := 18
    preStateRoot := ⟨1⟩ }

/-- A third request, for the second schema's cell in a heterogeneous joint
turn: same domain, its own target and digests, pre-state root `⟨0⟩`. -/
def requestB : Request .object :=
  { request with
    target := ⟨7⟩
    argsDigest := ⟨26⟩
    effectsDigest := ⟨27⟩
    nonce := 28
    preStateRoot := ⟨0⟩ }

/-! ## The authority token exists -/

/-- Proof-mode evidence at the permissive portal. -/
def evidence : Evidence permissivePortal authState request :=
  .proof () rfl

/-- **`Authorized` is inhabited.**  This is the token every accepted effect in
the tree is indexed by. -/
def authorized : Authorized permissivePortal authState request where
  evidence := evidence
  policyWitness := ()
  policyEpochExact := rfl
  policyVerified := rfl

theorem authorized_nonempty :
    Nonempty (Authorized permissivePortal authState request) := ⟨authorized⟩

/-- The same authority, granted for the second request. -/
def authorizedTrue : Authorized permissivePortal authState requestTrue where
  evidence := .proof () rfl
  policyWitness := ()
  policyEpochExact := rfl
  policyVerified := rfl

/-- The same authority, granted for the second schema's request. -/
def authorizedB : Authorized permissivePortal authState requestB where
  evidence := .proof () rfl
  policyWitness := ()
  policyEpochExact := rfl
  policyVerified := rfl

/-! ## Teeth -/

/-- **The policy gate is a real gate.**  Evidence still exists at
`policyClosedPortal` -- every verifier but the policy one accepts -- and
`Authorized` is nevertheless empty.  Authority does not follow from evidence.
-/
theorem evidence_exists_at_policyClosedPortal :
    Nonempty (Evidence policyClosedPortal authState request) :=
  ⟨.proof () rfl⟩

theorem authorized_isEmpty_of_policyClosed :
    IsEmpty (Authorized policyClosedPortal authState request) :=
  ⟨fun token => by
    have rejected : policyClosedPortal.verifyPolicy request token.policyWitness
        = false := rfl
    rw [token.policyVerified] at rejected
    exact Bool.noConfusion rejected⟩

/-- A request quoting a stale policy epoch: the state moved to epoch `1` and
the request still says `0`. -/
def rotatedState : AuthState :=
  { authState with policyEpoch := fun _ => 1 }

/-- **The epoch equation is a real equation.**  At the fully permissive portal,
with evidence available, a request whose quoted policy epoch is not the state's
cannot be authorized. -/
theorem evidence_exists_at_rotatedState :
    Nonempty (Evidence permissivePortal rotatedState request) :=
  ⟨.proof () rfl⟩

theorem authorized_isEmpty_of_staleEpoch :
    IsEmpty (Authorized permissivePortal rotatedState request) :=
  ⟨fun token => by
    have stale : request.policyEpoch = rotatedState.policyEpoch request.policyId :=
      token.policyEpochExact
    exact absurd stale (by decide)⟩

/-- info: 'Minidregg.Theory.TypedAuthorizationWitness.authorized_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorized_nonempty
/-- info: 'Minidregg.Theory.TypedAuthorizationWitness.evidence_exists_at_policyClosedPortal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evidence_exists_at_policyClosedPortal
/-- info: 'Minidregg.Theory.TypedAuthorizationWitness.authorized_isEmpty_of_policyClosed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorized_isEmpty_of_policyClosed
/-- info: 'Minidregg.Theory.TypedAuthorizationWitness.evidence_exists_at_rotatedState' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evidence_exists_at_rotatedState
/-- info: 'Minidregg.Theory.TypedAuthorizationWitness.authorized_isEmpty_of_staleEpoch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorized_isEmpty_of_staleEpoch

end Minidregg.Theory.TypedAuthorizationWitness
