/-
# Compiler.SemanticController — Lean-owned control around opaque native compute

The native boundary in this module is deliberately only an arbitrary function

  `KernelQuery → KernelReply`.

A reply is bounded first-order data: an echoed request/challenge, a fixed result
word, and a fixed descriptor-wire vector.  It has no Boolean accept bit and no
`Verified` constructor.  Lean owns authorization, phase order, canonical request
encoding, challenge derivation, result equality, descriptor-prefix binding, the
descriptor check, and the sole proof-relevant `Verified` token.

`arbitraryOracle_integrity` quantifies over every native oracle.  If the
controller reaches `Verified`, the existing `BoundSemanticReceiptRelation` and
the existing emitted-descriptor acceptance statement hold.  There is no native
semantics and no native-refinement theorem here.
-/
import Compiler.SemanticTurnReceiptDescriptor
import Theory.AuthorizationDeclaration
import Theory.IndexedProgram

namespace Minidregg.Compiler.SemanticController

open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ReactiveReceipt
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Compiler.SemanticTurnReceiptDescriptor

abbrev ReceiptDeclaration :=
  Minidregg.Compiler.SemanticTurnReceiptDescriptor.Declaration

/-! ## 1. Canonical context and deterministic challenge -/

/-- Controller input.  The request itself remains the index of the existing
authorization presentation.  Its first-order form is always derived by
`Context.requestWire`; callers cannot supply a divergent encoded request. -/
structure Context
    (decl : ReceiptDeclaration)
    (portal : Portal) (state : AuthState)
    {kind : ResourceKind} (request : Request kind) where
  presentation : Presentation portal request
  witness : BoundReceiptWitness decl.keyCount BabyBear

/-- The canonical request is projected through the existing lawful declaration
codec, never copied into controller input. -/
def Context.requestWire
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (_ : Context decl portal state request) : RequestWire :=
  encodeRequest ⟨kind, request⟩

/-- A controller challenge binds the two declaration versions, exact request,
fixed state width, and the sixteen header-binding cells.  This is a deterministic
control challenge, not a claim of cryptographic Fiat--Shamir security. -/
structure Challenge (decl : ReceiptDeclaration) where
  authorizationSchemaVersion : Nat
  receiptSchemaVersion : Nat
  request : RequestWire
  keyCount : Nat
  binding : BindingIx → BabyBear

/-- Executable, finite equality test for challenges.  This avoids obtaining
decidability from classical equality of function fields. -/
def Challenge.Matches {decl : ReceiptDeclaration}
    (left right : Challenge decl) : Prop :=
  left.authorizationSchemaVersion = right.authorizationSchemaVersion ∧
  left.receiptSchemaVersion = right.receiptSchemaVersion ∧
  left.request = right.request ∧
  left.keyCount = right.keyCount ∧
  ∀ index : BindingIx, left.binding index = right.binding index

instance Challenge.instDecidableMatches {decl : ReceiptDeclaration}
    (left right : Challenge decl) : Decidable (left.Matches right) := by
  unfold Challenge.Matches
  infer_instance

theorem Challenge.eq_of_matches {decl : ReceiptDeclaration}
    {left right : Challenge decl} (h : left.Matches right) :
    left = right := by
  rcases h with ⟨hauthorization, hreceipt, hrequest, hkeys, hbinding⟩
  cases left with
  | mk leftAuthorization leftReceipt leftRequest leftKeys leftBinding =>
      cases right with
      | mk rightAuthorization rightReceipt rightRequest rightKeys rightBinding =>
          simp only at hauthorization hreceipt hrequest hkeys hbinding
          subst rightAuthorization
          subst rightReceipt
          subst rightRequest
          subst rightKeys
          congr
          funext index
          exact hbinding index

/-- Lean-owned challenge derivation from the canonical context. -/
def Context.challenge
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (ctx : Context decl portal state request) : Challenge decl where
  authorizationSchemaVersion := declaration.schemaVersion
  receiptSchemaVersion := semanticReceiptVersion
  request := ctx.requestWire
  keyCount := decl.keyCount
  binding := ctx.witness.binding

/-! ## 2. Bounded native query/reply data — no acceptance -/

/-- Everything opaque compute receives is chosen by Lean.  The emitted
descriptor is data inside the query; downstream code does not author it. -/
structure KernelQuery (decl : ReceiptDeclaration) where
  request : RequestWire
  challenge : Challenge decl
  descriptor : ConstraintDescriptor BabyBear

/-- A reply contains only bounded data.

* `result` has exactly the declaration's variable width;
* `proofWires` has exactly the emitted descriptor's total wire width.

There is intentionally no `accepted : Bool`, proof of a proposition, or token. -/
structure KernelReply (decl : ReceiptDeclaration) where
  requestEcho : RequestWire
  challengeEcho : Challenge decl
  result : decl.WireIx → BabyBear
  proofWires : Fin (descriptor decl).nWires → BabyBear

/-- Read a finite reply as the total vector expected by `descriptorHolds`.
Out-of-range coordinates are zero and cannot be mentioned by a well-formed
emitted descriptor. -/
def KernelReply.totalWires
    {decl : ReceiptDeclaration} (reply : KernelReply decl) :
    Nat → BabyBear := fun index =>
  if h : index < (descriptor decl).nWires then
    reply.proofWires ⟨index, h⟩
  else 0

/-- The native boundary is completely opaque and universally quantified in the
integrity theorem. -/
abbrev NativeOracle (decl : ReceiptDeclaration) :=
  KernelQuery decl → KernelReply decl

def Context.query
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (ctx : Context decl portal state request) (challenge : Challenge decl) :
    KernelQuery decl where
  request := ctx.requestWire
  challenge := challenge
  descriptor := descriptor decl

/-! ## 3. Lean-only checks and the sole verified token -/

inductive RejectReason
  | authorization (failedCheck : Check)
  | issuedChallengeMismatch
  | requestEchoMismatch
  | challengeEchoMismatch
  | resultMismatch
  | proofPrefixMismatch
  | descriptorRejected
deriving DecidableEq, Repr

/-- Proof-relevant success.  Its fields are the existing authorization object,
existing emitted-descriptor acceptance, and existing bound receipt relation.
The reply itself cannot construct this structure. -/
structure Verified
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (ctx : Context decl portal state request) where
  authorization : Nonempty (Authorized portal state request)
  reply : KernelReply decl
  issuedChallengeExact : reply.challengeEcho = ctx.challenge
  requestExact : reply.requestEcho = ctx.requestWire
  resultExact : reply.result = boundRuntimeEncode ctx.witness
  descriptorAcceptance :
    ∃ wireValues : Nat → BabyBear,
      (∀ index : decl.WireIx,
        wireValues index.val = boundRuntimeEncode ctx.witness index) ∧
      descriptorHolds (descriptor decl) wireValues
  relation : BoundSemanticReceiptRelation ctx.witness.encode

inductive Outcome
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (ctx : Context decl portal state request)
  | rejected (reason : RejectReason)
  | verified (token : Verified ctx)

/-- Proposition used to state controller reachability without exposing a second
acceptance API. -/
def Outcome.IsVerified
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    {ctx : Context decl portal state request} : Outcome ctx → Prop
  | .rejected _ => False
  | .verified _ => True

/-- All result/proof checks are performed here in Lean.  The authorization
object is supplied only by the preceding authorization phase. -/
def checkReply
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (ctx : Context decl portal state request)
    (authorization : Nonempty (Authorized portal state request))
    (issued : Challenge decl) (reply : KernelReply decl) : Outcome ctx := by
  exact if hissued : issued.Matches ctx.challenge then
    if hrequest : reply.requestEcho = ctx.requestWire then
      if hchallenge : reply.challengeEcho.Matches issued then
        if hresult : ∀ index : decl.WireIx,
            reply.result index = boundRuntimeEncode ctx.witness index then
          if hprefix : ∀ index : decl.WireIx,
              reply.totalWires index.val = reply.result index then
            if hdescriptor : descriptorHolds
                (descriptor decl) reply.totalWires then
              let descriptorAcceptance :
                  ∃ wireValues : Nat → BabyBear,
                    (∀ index : decl.WireIx,
                      wireValues index.val =
                        boundRuntimeEncode ctx.witness index) ∧
                    descriptorHolds
                      (descriptor decl) wireValues := by
                refine ⟨reply.totalWires, ?_, hdescriptor⟩
                intro index
                exact (hprefix index).trans (hresult index)
              .verified
                { authorization := authorization
                  reply := reply
                  issuedChallengeExact :=
                    (Challenge.eq_of_matches hchallenge).trans
                      (Challenge.eq_of_matches hissued)
                  requestExact := hrequest
                  resultExact := funext hresult
                  descriptorAcceptance := descriptorAcceptance
                  relation :=
                    (descriptor_accepts_iff_boundRelation
                      decl ctx.witness).mp descriptorAcceptance }
            else .rejected .descriptorRejected
          else .rejected .proofPrefixMismatch
        else .rejected .resultMismatch
      else .rejected .challengeEchoMismatch
    else .rejected .requestEchoMismatch
  else .rejected .issuedChallengeMismatch

/-! ## 4. Response-indexed phase machine -/

inductive Phase
  | authorization
  | challenge
  | native
  | checking
  | done
deriving DecidableEq, Repr

/-- Authorization response is produced by Lean's existing executable plan.  An
accepted response carries the equality needed to construct `Authorized`; a
native reply can never inhabit this type. -/
inductive AuthorizationResponse
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (presentation : Presentation portal request)
  | accepted
      (authorization : Nonempty (Authorized portal state request))
  | rejected (failedCheck : Check)

inductive ControllerOp
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (ctx : Context decl portal state request) : Phase → Type
  | authorize : ControllerOp ctx .authorization
  | deriveChallenge : ControllerOp ctx .challenge
  | invoke (query : KernelQuery decl) : ControllerOp ctx .native
  | validate
      (authorization : Nonempty (Authorized portal state request))
      (issued : Challenge decl) (reply : KernelReply decl) :
      ControllerOp ctx .checking

/-- The indexed signature makes phase order a type-level fact. -/
def controllerSignature
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (ctx : Context decl portal state request) : IxSignature Phase where
  Op := ControllerOp ctx
  Resp := fun op => match op with
    | .authorize =>
        @AuthorizationResponse portal state kind request ctx.presentation
    | .deriveChallenge => Challenge decl
    | .invoke _ => KernelReply decl
    | .validate _ _ _ => Outcome ctx
  next := fun op => match op with
    | .authorize => fun response => match response with
        | .accepted _ => .challenge
        | .rejected _ => .done
    | .deriveChallenge => fun _ => .native
    | .invoke _ => fun _ => .checking
    | .validate _ _ _ => fun _ => .done

abbrev ControllerResult
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (ctx : Context decl portal state request) : Phase → Type :=
  fun _ => Outcome ctx

/-- The only legal controller order:

authorization → challenge derivation → native invocation → Lean validation.
-/
def program
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (ctx : Context decl portal state request) :
    Program (controllerSignature ctx) (ControllerResult ctx) .authorization :=
  .call (@ControllerOp.authorize decl portal state kind request ctx) fun
    | .rejected failed => .pure (.rejected (.authorization failed))
    | .accepted authorization =>
        .call .deriveChallenge fun challenge =>
          .call (.invoke (ctx.query challenge)) fun reply =>
            .call (.validate authorization challenge reply) fun outcome =>
              .pure outcome

/-! ## 5. Fixed Lean handler around an arbitrary native oracle -/

/-- The handler is fixed except for `oracle`.  Authorization, challenge
derivation, and validation are all Lean functions; only `.invoke` calls the
opaque boundary. -/
def handler
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (ctx : Context decl portal state request) (oracle : NativeOracle decl) :
    Handler (controllerSignature ctx) (fun _ => Unit) where
  handle := fun op _ => match (show ControllerOp ctx _ from op) with
    | ControllerOp.authorize =>
        match checked : verify (state := state) ctx.presentation with
        | .accepted =>
            ⟨.accepted
              (verify_accepted_authorized ctx.presentation checked), ()⟩
        | .rejected failed => ⟨.rejected failed, ()⟩
    | ControllerOp.deriveChallenge => ⟨ctx.challenge, ()⟩
    | ControllerOp.invoke query => ⟨oracle query, ()⟩
    | ControllerOp.validate authorization issued reply =>
        ⟨checkReply ctx authorization issued reply, ()⟩

/-- Execute the typed controller.  The dependent final phase is hidden because
`ControllerResult` is the same outcome type at every phase. -/
def run
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (ctx : Context decl portal state request) (oracle : NativeOracle decl) :
    Outcome ctx :=
  (interpret (handler ctx oracle) (program ctx) ()).2.1

/-! ## 6. Arbitrary-oracle integrity and teeth -/

/-- **Arbitrary-oracle integrity.** No property of `oracle` is assumed.  If the
controller reaches its sole verified outcome, authorization exists and both the
existing accumulated receipt relation and emitted descriptor acceptance hold. -/
theorem arbitraryOracle_integrity
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (ctx : Context decl portal state request) (oracle : NativeOracle decl)
    (reached : (run ctx oracle).IsVerified) :
    Nonempty (Authorized portal state request) ∧
      BoundSemanticReceiptRelation ctx.witness.encode ∧
      ∃ wireValues : Nat → BabyBear,
        (∀ index : decl.WireIx,
          wireValues index.val = boundRuntimeEncode ctx.witness index) ∧
        descriptorHolds (descriptor decl) wireValues := by
  cases hrun : run ctx oracle with
  | rejected reason => simp [Outcome.IsVerified, hrun] at reached
  | verified token =>
      exact ⟨token.authorization, token.relation, token.descriptorAcceptance⟩

/-- A reply naming a different result can never become verified, regardless of
its proof wires or the native oracle that produced it. -/
theorem resultMismatch_not_verified
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (ctx : Context decl portal state request)
    (authorization : Nonempty (Authorized portal state request))
    (issued : Challenge decl) (reply : KernelReply decl)
    (mismatch : reply.result ≠ boundRuntimeEncode ctx.witness) :
    ¬ (checkReply ctx authorization issued reply).IsVerified := by
  have hpointwise : ¬ ∀ index : decl.WireIx,
      reply.result index = boundRuntimeEncode ctx.witness index := by
    intro equalAt
    apply mismatch
    funext index
    exact equalAt index
  by_cases hissued : issued.Matches ctx.challenge
  · by_cases hrequest : reply.requestEcho = ctx.requestWire
    · by_cases hchallenge : reply.challengeEcho.Matches issued
      · simp [checkReply, hissued, hrequest, hchallenge, hpointwise,
          Outcome.IsVerified]
      · simp [checkReply, hissued, hrequest, hchallenge, Outcome.IsVerified]
    · simp [checkReply, hissued, hrequest, Outcome.IsVerified]
  · simp [checkReply, hissued, Outcome.IsVerified]

/-- Even a perfectly echoed result cannot promote proof wires that fail the
Lean-emitted descriptor. -/
theorem descriptorFailure_not_verified
    {decl : ReceiptDeclaration}
    {portal : Portal} {state : AuthState}
    {kind : ResourceKind} {request : Request kind}
    (ctx : Context decl portal state request)
    (authorization : Nonempty (Authorized portal state request))
    (issued : Challenge decl) (reply : KernelReply decl)
    (failure : ¬ descriptorHolds
      (descriptor decl) reply.totalWires) :
    ¬ (checkReply ctx authorization issued reply).IsVerified := by
  by_cases hissued : issued.Matches ctx.challenge
  · by_cases hrequest : reply.requestEcho = ctx.requestWire
    · by_cases hchallenge : reply.challengeEcho.Matches issued
      · by_cases hresult : ∀ index : decl.WireIx,
          reply.result index = boundRuntimeEncode ctx.witness index
        · by_cases hprefix : ∀ index : decl.WireIx,
            reply.totalWires index.val = boundRuntimeEncode ctx.witness index
          · simp [checkReply, hissued, hrequest, hchallenge, hresult,
              hprefix, failure, Outcome.IsVerified]
          · simp [checkReply, hissued, hrequest, hchallenge, hresult,
              hprefix, Outcome.IsVerified]
        · simp [checkReply, hissued, hrequest, hchallenge, hresult,
            Outcome.IsVerified]
      · simp [checkReply, hissued, hrequest, hchallenge, Outcome.IsVerified]
    · simp [checkReply, hissued, hrequest, Outcome.IsVerified]
  · simp [checkReply, hissued, Outcome.IsVerified]

/-- info: 'Minidregg.Compiler.SemanticController.arbitraryOracle_integrity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms arbitraryOracle_integrity
/-- info: 'Minidregg.Compiler.SemanticController.resultMismatch_not_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resultMismatch_not_verified
/-- info: 'Minidregg.Compiler.SemanticController.descriptorFailure_not_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms descriptorFailure_not_verified

end Minidregg.Compiler.SemanticController
