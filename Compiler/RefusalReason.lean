/-
# Compiler.RefusalReason -- the closed set of named Host refusals

A Host refusal names the admission branch that decided it. The outcome codec
commits to the name (one tag byte), never to prose, so a client renders the
reason from data. Detail text is fixed per reason on the observation path; it
carries a controller's typed `Reject` only for `operationRejected`, which is
reached after the requester's read authority has been established.

A `lawDenied` refusal also carries the clause of the law that failed
(`LawLeaf`): its path in the committed law, the clause itself and the values
of its slot in the two views the law read. It is computed by
`Pred.firstFailingLeaf` on the same projected step the law was evaluated on,
so it is an explanation of that evaluation, not a second decision
(`LawLeaf.of_none_iff`, `LawLeaf.of_fails`).

Disclosure order. A requester learns only what it is entitled to learn:

* before its key is selected, only `malformed` or `unknownKey` (enrollment is
  a public coordinate of the challenge);
* a challenge that no longer matches the current world root, authority root
  or height is `staleRoot` (all three are public challenge fields);
* after its signature verifies, every capability failure up to and including
  holder coverage and native use is `noGrant`. Absent, stolen, out-of-scope
  and other-target capabilities are therefore indistinguishable, so a key
  cannot probe another holder's revocation, validity window or epochs;
* only a covered holder with a verified use learns `revoked`,
  `outsideValidity`, `staleGrant` or `lawDenied`.

Blind submission keeps its uniform refusal (`undisclosed`); see
`NativeHost.publicSubmissionOutcome`.
-/
import Compiler.Tower256ConcreteBackend
import Compiler.CredentialSignatureAdmission
import Theory.AuthorizationDeclaration
import Compiler.PolicyRecordCodec
import Pred.Leaf

namespace Minidregg.Compiler

open Minidregg.Theory
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

inductive RefusalReason where
  /-- The request does not decode, or does not match the operation it names. -/
  | malformed
  /-- The requesting subject has no enrolled, usable current key. -/
  | unknownKey
  /-- The signed challenge or plan names a world root, authority read or height that is no longer current. -/
  | staleRoot
  /-- The signature does not verify for the selected key and exact request. -/
  | badSignature
  /-- No capability held by this key covers this target and operation. -/
  | noGrant
  /-- The held capability, one of its ancestors, or one of its channels is revoked. -/
  | revoked
  /-- The request height is outside the held capability's validity window. -/
  | outsideValidity
  /-- The held capability's issuer or policy epoch is no longer current. -/
  | staleGrant
  /-- The resource's current committed law denies this operation. -/
  | lawDenied
  /-- Authorized, but the operation's controller or receiver refused it. -/
  | operationRejected
  /-- A different transaction already holds this transaction identity. -/
  | conflict
  /-- A blind submission was refused; by design no state-dependent reason is disclosed. -/
  | undisclosed
  deriving DecidableEq, Repr, Inhabited

namespace RefusalReason

/-- Stable wire and display name. -/
def name : RefusalReason → String
  | .malformed => "malformed"
  | .unknownKey => "unknown-key"
  | .staleRoot => "stale-root"
  | .badSignature => "bad-signature"
  | .noGrant => "no-grant"
  | .revoked => "revoked"
  | .outsideValidity => "outside-validity"
  | .staleGrant => "stale-grant"
  | .lawDenied => "law-denied"
  | .operationRejected => "operation-rejected"
  | .conflict => "conflict"
  | .undisclosed => "undisclosed"

/-- Fixed friend-facing text. It depends on the reason only. -/
def describe : RefusalReason → String
  | .malformed => "the request does not decode or does not match its operation"
  | .unknownKey => "this key is not enrolled on this Host"
  | .staleRoot => "the Host state moved since the challenge; observe again"
  | .badSignature => "the signature does not verify for this key and request"
  | .noGrant => "this key holds no grant covering this target and operation"
  | .revoked => "the grant, one of its ancestors, or one of its channels is revoked"
  | .outsideValidity => "the request is outside the grant's validity window"
  | .staleGrant => "the grant's issuer or policy epoch is no longer current"
  | .lawDenied => "the resource's current law denies this operation"
  | .operationRejected => "the operation was refused by its controller"
  | .conflict => "transaction identity conflict"
  | .undisclosed => "request refused; a blind submission discloses no reason"

def all : List RefusalReason :=
  [.malformed, .unknownKey, .staleRoot, .badSignature, .noGrant, .revoked,
    .outsideValidity, .staleGrant, .lawDenied, .operationRejected, .conflict, .undisclosed]

theorem mem_all (reason : RefusalReason) : reason ∈ all := by
  cases reason <;> decide

/-- Names are pairwise distinct, so the rendered name identifies the reason. -/
theorem name_injective : Function.Injective name := by
  intro left right same
  cases left <;> cases right <;> first | rfl | (simp [name] at same)

/-- One tag byte. An unknown tag refuses to decode. -/
def stream : StreamCodec RefusalReason where
  encode
    | .malformed => [0]
    | .unknownKey => [1]
    | .staleRoot => [2]
    | .badSignature => [3]
    | .noGrant => [4]
    | .revoked => [5]
    | .outsideValidity => [6]
    | .staleGrant => [7]
    | .lawDenied => [8]
    | .operationRejected => [9]
    | .conflict => [10]
    | .undisclosed => [11]
  decodePrefix
    | 0 :: suffix => some (.malformed, suffix)
    | 1 :: suffix => some (.unknownKey, suffix)
    | 2 :: suffix => some (.staleRoot, suffix)
    | 3 :: suffix => some (.badSignature, suffix)
    | 4 :: suffix => some (.noGrant, suffix)
    | 5 :: suffix => some (.revoked, suffix)
    | 6 :: suffix => some (.outsideValidity, suffix)
    | 7 :: suffix => some (.staleGrant, suffix)
    | 8 :: suffix => some (.lawDenied, suffix)
    | 9 :: suffix => some (.operationRejected, suffix)
    | 10 :: suffix => some (.conflict, suffix)
    | 11 :: suffix => some (.undisclosed, suffix)
    | _ => none
  decodePrefix_encode := by intro value suffix; cases value <;> rfl

theorem stream_unknown_tag (suffix : List UInt8) :
    stream.decodePrefix (12 :: suffix) = none := rfl

/-- The signature adapter's typed rejection, named. Key absence, unusable key
records and a key version that is unregistered or revoked (its standing in the
authority cell) are `unknownKey`: the subject has no usable current key. A
moved subject-key epoch, a signed footprint whose authority read has changed,
and a plan past its signed `validUntil` height are `staleRoot`: the signed plan
no longer describes the current state. A footprint that does not decode is
`malformed`; every envelope and binding failure is `badSignature`. -/
def ofSignature : CredentialSignatureAdmission.Reject → RefusalReason
  | .wrongDomain => .malformed
  | .missingCurrentKey => .unknownKey
  | .subjectKeyEpoch => .staleRoot
  | .unregisteredKey => .unknownKey
  | .revokedKey => .unknownKey
  | .unsupportedAlgorithm => .unknownKey
  | .publicKeyLength => .unknownKey
  | .envelope _ => .badSignature
  | .sourceBinding => .badSignature
  | .malformedFootprint => .malformed
  | .footprintStale _ => .staleRoot
  | .expired _ _ => .staleRoot

theorem ofSignature_missingCurrentKey :
    ofSignature .missingCurrentKey = .unknownKey := rfl

theorem ofSignature_envelope
    (failure : Kernel.CredentialSignedEnvelopeController.Failure CredentialSignatureIO.Error) :
    ofSignature (.envelope failure) = .badSignature := rfl

/-! ## Capability admission, component by component -/

/-- The policy-id half of `TargetSet.RequestLaw`: an explicit capability is
used only under the law it was issued under; an `under R` capability carries
no request-law binding (the target's own law is evaluated by the controller). -/
def requestLawPolicyCheck {kind : ResourceKind} (cap : Capability kind)
    (request : Request kind) : Bool :=
  match cap.scope.targets with
  | .explicit _ => decide (cap.policyId = request.policyId)
  | .under _ => true

/-- The epoch half of `TargetSet.RequestLaw`. -/
def requestLawEpochCheck {kind : ResourceKind} (cap : Capability kind)
    (request : Request kind) : Bool :=
  match cap.scope.targets with
  | .explicit _ => decide (cap.policyEpoch = request.policyEpoch)
  | .under _ => true

theorem requestLaw_checks_iff {kind : ResourceKind} (cap : Capability kind)
    (request : Request kind) :
    (requestLawPolicyCheck cap request && requestLawEpochCheck cap request) =
      decide (cap.scope.targets.RequestLaw cap.policyId cap.policyEpoch request) := by
  unfold requestLawPolicyCheck requestLawEpochCheck
  cases cap.scope.targets <;> simp [TargetSet.RequestLaw]

/-- Every component of `Capability.Admissible`, in exactly the order that
`capabilityAdmissibleCheck` evaluates it, each paired with the reason its
failure is reported under. Holder and scope come first, so a key that does
not hold the capability learns only `noGrant`. -/
def capabilityChecks {kind : ResourceKind} (cap : Capability kind) (state : AuthState)
    (request : Request kind) : List (RefusalReason × Bool) :=
  [(.noGrant, holderCoversCheck cap.holder request.subject),
   (.noGrant, scopeCoversCheck cap.scope state.parent request),
   (.outsideValidity, decide (cap.notBefore ≤ request.height)),
   (.outsideValidity, decide (request.height ≤ cap.notAfter)),
   (.noGrant, requestLawPolicyCheck cap request),
   (.staleGrant, requestLawEpochCheck cap request),
   (.staleGrant, decide (cap.policyEpoch = state.policyEpoch cap.policyId)),
   (.staleGrant, decide (cap.issuerEpoch = state.issuerEpoch cap.issuer)),
   (.revoked, decide (RevocationKey.capability cap.id ∉ state.revoked)),
   (.revoked, capabilityIdsUnrevoked state cap.ancestors),
   (.revoked, channelIdsUnrevoked state cap.channels)]

/-- The first failing component's reason; `none` exactly when admissible. -/
def capabilityRefusal {kind : ResourceKind} (cap : Capability kind) (state : AuthState)
    (request : Request kind) : Option RefusalReason :=
  ((capabilityChecks cap state request).find? (fun check => !check.2)).map Prod.fst

private theorem firstFailure_none_iff (checks : List (RefusalReason × Bool)) :
    (checks.find? (fun check => !check.2)).map Prod.fst = none ↔
      (checks.map Prod.snd).all (fun accepted => accepted) = true := by
  induction checks with
  | nil => simp
  | cons head tail ih =>
      obtain ⟨reason, accepted⟩ := head
      cases accepted <;> simp [ih]

/-- The classifier is the existing admission decision, not a second one: it
reports no reason exactly when `capabilityAdmissibleCheck` accepts. -/
theorem capabilityRefusal_eq_none_iff {kind : ResourceKind} (cap : Capability kind)
    (state : AuthState) (request : Request kind) :
    capabilityRefusal cap state request = none ↔
      capabilityAdmissibleCheck cap state request = true := by
  unfold capabilityRefusal
  rw [firstFailure_none_iff, capabilityAdmissibleCheck, ← requestLaw_checks_iff]
  simp [capabilityChecks, Bool.and_assoc]

theorem capabilityRefusal_eq_none_iff_admissible {kind : ResourceKind}
    (cap : Capability kind) (state : AuthState) (request : Request kind) :
    capabilityRefusal cap state request = none ↔ cap.Admissible state request := by
  rw [capabilityRefusal_eq_none_iff, capabilityAdmissibleCheck_eq_true_iff]

/-- A capability whose holder does not cover the requester is reported as
`noGrant`, whatever else is true of it (revoked, expired or stale). -/
theorem capabilityRefusal_holder {kind : ResourceKind} (cap : Capability kind)
    (state : AuthState) (request : Request kind)
    (foreign : holderCoversCheck cap.holder request.subject = false) :
    capabilityRefusal cap state request = some .noGrant := by
  simp [capabilityRefusal, capabilityChecks, foreign]

/-! ## Both poles on concrete instances -/

namespace Sample

def owner : SubjectId := ⟨7⟩
def thief : SubjectId := ⟨9⟩
def target : ResourceId .object := ⟨42⟩

def state (revoked : Finset RevocationKey) (policyEpoch : Epoch) : AuthState where
  capabilityRoot := ⟨0⟩
  revocationRoot := ⟨0⟩
  policyRoot := ⟨0⟩
  policyAddress := fun _ _ => ⟨0⟩
  revoked := revoked
  issuerEpoch := fun _ => 0
  policyEpoch := fun _ => policyEpoch
  policyRevision := fun _ => 0
  subjectKeyEpoch := fun _ => 0
  parent := Parentage.empty

def grant (notAfter : Height) : Capability .object where
  id := ⟨100⟩
  root := ⟨100⟩
  parent := none
  issuer := ⟨1⟩
  holder := .subject owner
  scope := ⟨.explicit {target}, {.observeObject}, 1000, none, ∅⟩
  notBefore := 0
  notAfter := notAfter
  issuerEpoch := 0
  policyId := ⟨42⟩
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

def read (subject : SubjectId) (height : Height) : Request .object where
  domain := ⟨0⟩
  semantics := ⟨0⟩
  federation := ⟨0⟩
  subject := subject
  subjectKeyEpoch := 0
  target := target
  verb := .observeObject
  argsDigest := ⟨0⟩
  effectsDigest := ⟨0⟩
  nonce := 0
  height := height
  preStateRoot := ⟨0⟩
  policyId := ⟨42⟩
  policyEpoch := 0
  policyRevision := 0
  cost := 10

end Sample

open Sample in
theorem sample_admitted :
    capabilityRefusal (grant 50) (state ∅ 0) (read owner 5) = none := by decide

open Sample in
theorem sample_foreign_holder_noGrant :
    capabilityRefusal (grant 50) (state ∅ 0) (read thief 5) = some .noGrant := by decide

open Sample in
/-- A thief presenting a revoked capability still learns only `noGrant`. -/
theorem sample_foreign_revoked_noGrant :
    capabilityRefusal (grant 50) (state {.capability ⟨100⟩} 0) (read thief 5) =
      some .noGrant := by decide

open Sample in
theorem sample_revoked :
    capabilityRefusal (grant 50) (state {.capability ⟨100⟩} 0) (read owner 5) =
      some .revoked := by decide

open Sample in
theorem sample_outsideValidity :
    capabilityRefusal (grant 50) (state ∅ 0) (read owner 51) = some .outsideValidity := by decide

open Sample in
theorem sample_staleGrant :
    capabilityRefusal (grant 50) (state ∅ 1) { read owner 5 with policyEpoch := 1 } =
      some .staleGrant := by decide

open Sample in
theorem sample_other_target_noGrant :
    capabilityRefusal (grant 50) (state ∅ 0) { read owner 5 with target := ⟨43⟩ } =
      some .noGrant := by decide

open Sample in
/-- A room grant (`under 7`, issued under law 7) reaches cell 42 born in room 7
whose request names the cell's own law 42: no request-law binding applies. -/
theorem sample_room_admitted :
    capabilityRefusal { grant 50 with scope := ⟨.under 7, {.observeObject}, 1000, none, ∅⟩, policyId := ⟨7⟩ }
      { state ∅ 0 with parent := Parentage.ofList [(42, 7)] } (read owner 5) = none := by decide

open Sample in
/-- The same room grant does not reach a cell outside the room: `noGrant`. -/
theorem sample_room_outside_noGrant :
    capabilityRefusal { grant 50 with scope := ⟨.under 7, {.observeObject}, 1000, none, ∅⟩, policyId := ⟨7⟩ }
      { state ∅ 0 with parent := Parentage.ofList [(42, 8)] } (read owner 5) = some .noGrant := by decide

end RefusalReason

/-! ## The failing clause of a law -/

open Minidregg.Pred in
/-- The clause a `lawDenied` refusal names: its path from the root of the committed law, the
clause, and the values its slot had in the old and new views the law read (`none` for a
clause without a slot, or for an absent slot). -/
structure LawLeaf where
  path : List Nat
  clause : Pred
  before : Option Int
  after : Option Int
  deriving DecidableEq, Repr

namespace LawLeaf

open Minidregg.Pred

/-- The write guard (`request/verb` 2 is `write`, `CredentialAuthorityEntryCodec.verbTag`). -/
def writeGuard : Pred := .not (.eq "request/verb" 2)

/-- The clause as its author wrote it: a disjunction's write guards are dropped, and a
guarded single clause is that clause. On a refused write every guard is false, so it is
never the reason. -/
def explained : Pred → Pred
  | .anyL ps =>
      match ps.toList.filter (· != writeGuard) with
      | [clause] => if ps.toList.length = 1 then .anyL ps else clause
      | rest => if rest.length = ps.toList.length then .anyL ps else Pred.any rest
  | clause => clause

/-- The slot an explained clause reads: an atom's, or a negated atom's. -/
def slotOf : Pred → Option Slot
  | .eq s _ | .le s _ | .memberOf s _ | .writeOnce s | .monotone s => some s
  | .not (.eq s _) | .not (.le s _) | .not (.memberOf s _) | .not (.writeOnce s)
  | .not (.monotone s) => some s
  | _ => none

/-- The failing clause of `law` on the step `old → new`; `none` exactly when `eval` accepts. -/
def of (law : Pred) (old new : State) : Option LawLeaf := do
  let path ← firstFailingLeaf law old new
  let clause ← law.subterm path
  let slot := slotOf (explained clause)
  pure ⟨path, clause, slot.bind old.get, slot.bind new.get⟩

/-- A law names a clause exactly when it rejects the step. -/
theorem of_none_iff (law : Pred) (old new : State) :
    of law old new = none ↔ Minidregg.Pred.eval law old new = true := by
  rw [← firstFailingLeaf_none_iff_eval]
  unfold of
  cases named : firstFailingLeaf law old new with
  | none => simp
  | some path =>
      obtain ⟨clause, found, _, _⟩ := firstFailingLeaf_some_leaf law old new path named
      simp [found]

/-- The named clause sits in the law at its path, is a leaf, and is false on the same step. -/
theorem of_fails (law : Pred) (old new : State) (leaf : LawLeaf)
    (named : of law old new = some leaf) :
    law.subterm leaf.path = some leaf.clause ∧ leaf.clause.isLeaf = true ∧
      Minidregg.Pred.eval leaf.clause old new = false := by
  unfold of at named
  cases found : firstFailingLeaf law old new with
  | none => simp [found] at named
  | some path =>
      obtain ⟨clause, at_, isLeaf, fails⟩ := firstFailingLeaf_some_leaf law old new path found
      simp only [found, at_, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at named
      subst named
      exact ⟨at_, isLeaf, fails⟩

/-! ### Rendering, in the shell's law grammar

`field N` is `resource/field/N/after`; `field N before|delta` the other views;
`pair A,B delta`; `subject`, `verb`, `cost` the request slots, with verbs by name
(`read` 1, `write` 2, `delegate` 3, `install` 4, `revoke` 5: the tags `request/verb`
carries); any other slot is `slot "…"`. `sealed` is `any []`, `open` is `all []`;
lists are `[ a, b ]` and a negation is `not (X)`. -/

def renderSlot (slot : Slot) : String :=
  match slot.splitOn "/" with
  | ["resource", "field", n, "after"] => s!"field {n}"
  | ["resource", "field", n, "before"] => s!"field {n} before"
  | ["resource", "field", n, "delta"] => s!"field {n} delta"
  | ["resource", "pair", a, b, "delta"] => s!"pair {a},{b} delta"
  | ["request", "subject"] => "subject"
  | ["request", "verb"] => "verb"
  | ["request", "cost"] => "cost"
  | _ => s!"slot {slot.quote}"

def verbName : Int → String
  | 1 => "read"
  | 2 => "write"
  | 3 => "delegate"
  | 4 => "install"
  | 5 => "revoke"
  | value => toString value

def renderValue (slot : Slot) (value : Int) : String :=
  if slot = "request/verb" then verbName value else toString value

def renderSet (slot : Slot) (values : List Int) : String :=
  "{" ++ ",".intercalate (values.map (renderValue slot)) ++ "}"

mutual
def renderClause : Pred → String
  | .eq s v => s!"{renderSlot s} == {renderValue s v}"
  | .le s v => s!"{renderSlot s} <= {renderValue s v}"
  | .memberOf s xs => s!"{renderSlot s} in {renderSet s xs}"
  | .writeOnce s => s!"{renderSlot s} writeOnce"
  | .monotone s => s!"{renderSlot s} monotone"
  | .witnessed vk => s!"witnessed {vk.id.quote}"
  | .eqSlots a b => s!"{renderSlot a} == {renderSlot b}"
  | .leSlots a b => s!"{renderSlot a} <= {renderSlot b}"
  | .leSlotsOff a b k => s!"{renderSlot a} <= {renderSlot b} + {k}"
  | .not q => s!"not ({renderClause q})"
  | .allL .nil => "open"
  | .anyL .nil => "sealed"
  | .allL ps => s!"all [ {renderClauses ps} ]"
  | .anyL ps => s!"any [ {renderClauses ps} ]"
def renderClauses : PredList → String
  | .nil => ""
  | .cons q .nil => renderClause q
  | .cons q rest => s!"{renderClause q}, {renderClauses rest}"
end

private def shown : Option Int → String
  | some value => toString value
  | none => "absent"

/-- `field 2 monotone (before 2, after 1)`: the clause as its author wrote it, then the
values its slot had in the two views. -/
def render (leaf : LawLeaf) : String :=
  let clause := explained leaf.clause
  let values := match clause with
    | .monotone _ | .writeOnce _ =>
        s!" (before {shown leaf.before}, after {shown leaf.after})"
    | .eq _ _ | .le _ _ | .memberOf _ _ | .not _ =>
        if (slotOf clause).isSome then s!" (value {shown leaf.after})" else ""
    | _ => ""
  renderClause clause ++ values

/-! ### Wire form

The clause travels as the policy record's own token stream, so the refusal
names exactly the committed clause, never a paraphrase of it. -/

def predStream : StreamCodec Pred where
  encode clause := (StreamCodec.list PolicyRecordCodec.tokenStream).encode
    (PolicyRecordCodec.encodePred clause)
  decodePrefix bytes := do
    let (tokens, suffix) ← (StreamCodec.list PolicyRecordCodec.tokenStream).decodePrefix bytes
    let clause ← PolicyRecordCodec.decodePred tokens
    pure (clause, suffix)
  decodePrefix_encode := by
    intro clause suffix
    simp [StreamCodec.decodePrefix_encode, PolicyRecordCodec.decodePred_encode]

def stream : StreamCodec LawLeaf :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.list StreamCodec.nat)
      (StreamCodec.product predStream
        (StreamCodec.product (StreamCodec.option IntStream.intStream)
          (StreamCodec.option IntStream.intStream))))
    (fun leaf => (leaf.path, leaf.clause, leaf.before, leaf.after))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro leaf; cases leaf; rfl)

/-! ### The J13 refusal, rendered -/

theorem sample_refused_two_to_one :
    of LeafSample.boardLaw (LeafSample.before 2) (LeafSample.after 2 1) =
      some ⟨[0], LeafSample.onWrite (.monotone "resource/field/2/after"), some 2, some 1⟩ := by
  decide

/-- String rendering does not reduce in the kernel; the compiled evaluator checks it. -/
theorem sample_refused_rendered_compiled :
    render ⟨[0], LeafSample.onWrite (.monotone "resource/field/2/after"), some 2, some 1⟩ =
      "field 2 monotone (before 2, after 1)" := by native_decide

theorem sample_member_rendered_compiled :
    (of LeafSample.boardLaw (LeafSample.before 2) (LeafSample.after 2 5)).map render =
      some "field 2 in {0,1,2} (value 5)" := by native_decide

theorem sample_admitted_one_to_two :
    of LeafSample.boardLaw (LeafSample.before 1) (LeafSample.after 1 2) = none := by decide

theorem sample_sealed :
    of (Pred.any []) (LeafSample.read 1) (LeafSample.read 1) =
      some ⟨[], Pred.any [], none, none⟩ := by decide

theorem sample_sealed_rendered_compiled : render ⟨[], Pred.any [], none, none⟩ = "sealed" := by
  native_decide

/-- A guarded table drops only its guard; `field 0 after` is spelled `field 0`. -/
theorem sample_table_rendered_compiled :
    renderClause (explained (Pred.any [.eq "resource/field/0/delta" 0,
        Pred.all [.eq "resource/field/0/before" 0, .eq "resource/field/0/after" 1],
        .not (.eq "request/verb" 2)])) =
      "any [ field 0 delta == 0, all [ field 0 before == 0, field 0 == 1 ] ]" := by
  native_decide

theorem sample_management_rendered_compiled :
    renderClause (Pred.any [.eq "request/verb" 1, .eq "request/verb" 2,
        Pred.all [.memberOf "request/verb" [3, 4, 5], .eq "request/subject" 7]]) =
      "any [ verb == read, verb == write, all [ verb in {delegate,install,revoke}, subject == 7 ] ]" := by
  native_decide

end LawLeaf

/-- A named refusal with its display text, and for `lawDenied` the failing clause when the
deciding site could compute it. -/
structure Refusal where
  reason : RefusalReason
  detail : String
  leaf : Option LawLeaf := none
  deriving DecidableEq, Repr

/-- The fixed text for a reason; nothing state-dependent is added. -/
def Refusal.of (reason : RefusalReason) : Refusal := ⟨reason, reason.describe, none⟩

/-- A law refusal naming its failing clause. -/
def Refusal.lawDenied (leaf : Option LawLeaf) : Refusal :=
  ⟨.lawDenied, RefusalReason.lawDenied.describe, leaf⟩

instance : ToString Refusal := ⟨fun refusal => match refusal.leaf with
  | some leaf => s!"refused: {refusal.reason.name}: {leaf.render}"
  | none => s!"refused: {refusal.reason.name}: {refusal.detail}"⟩

end Minidregg.Compiler

#print axioms Minidregg.Compiler.RefusalReason.capabilityRefusal_eq_none_iff_admissible
#print axioms Minidregg.Compiler.RefusalReason.sample_admitted
#print axioms Minidregg.Compiler.RefusalReason.sample_revoked

/-- info: 'Minidregg.Compiler.LawLeaf.of_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Minidregg.Compiler.LawLeaf.of_fails

/-- info: 'Minidregg.Compiler.LawLeaf.of_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Minidregg.Compiler.LawLeaf.of_none_iff
