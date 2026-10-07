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
  `outsideValidity`, `staleGrant` or `lawDenied`;
* a `lawDenied` names its clause, path and slot values only through the slots the
  holder's grant covers (`Refusal.lawDeniedFor`, `refusal_leaf_depends_only_on_covered_fields`):
  a clause over a field outside a `--fields` grant is not named, and no such value is shown.

Before any of this, an observation request is authenticated: the subject's signature over
the intent's bytes is checked against its current key before a target is read
(`NativeObservationController.authenticated`), so a key that was never enrolled is answered
`unknownKey` or `badSignature`, whatever the intent names.

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
  /-- An order clause of the law compares two values further apart than the
  native order comparison decides (`NativeHostProfile.orderWidth`); the clause
  and its two values are named. Fail-closed: no verdict is guessed. -/
  | lawInputRange
  /-- Authorized, but the operation's controller or receiver refused it. -/
  | operationRejected
  /-- A different transaction already holds this transaction identity. -/
  | conflict
  /-- A blind submission was refused; by design no state-dependent reason is disclosed. -/
  | undisclosed
  /-- The node is more than its tail bound past its last certified head
  (`Kernel.TailBound`).  A fact about the public chain head, so it is named
  even on a blind submission (MR's rule): it says nothing about the request. -/
  | tailBound
  /-- Authorized, but the target object's audience moved: a holder of its
  current epoch no longer stands (the all-holder gate,
  `DeclaredResourceController.checkTargetAudience`), so no fresh protected bytes
  are admitted until the owner rotates the epoch. Like `operationRejected` it is
  reached only after the requester's read authority is established; a blind
  submission still tells it as `undisclosed`. -/
  | audienceTransition
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
  | .lawInputRange => "law-input-range"
  | .operationRejected => "operation-rejected"
  | .conflict => "conflict"
  | .undisclosed => "undisclosed"
  | .tailBound => "tail-bound"
  | .audienceTransition => "audience-transition"

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
  | .lawInputRange => "a law clause compares two values outside the native order range"
  | .operationRejected => "the operation was refused by its controller"
  | .conflict => "transaction identity conflict"
  | .undisclosed => "request refused; a blind submission discloses no reason"
  | .tailBound => "the node is past its tail bound; no write is admitted until the next checkpoint"
  | .audienceTransition => "a holder of the object's current audience epoch no longer stands; the owner rotates the epoch before new protected bytes"

def all : List RefusalReason :=
  [.malformed, .unknownKey, .staleRoot, .badSignature, .noGrant, .revoked,
    .outsideValidity, .staleGrant, .lawDenied, .operationRejected, .conflict, .undisclosed,
    .lawInputRange, .tailBound, .audienceTransition]

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
    | .lawInputRange => [12]
    | .tailBound => [13]
    | .audienceTransition => [14]
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
    | 12 :: suffix => some (.lawInputRange, suffix)
    | 13 :: suffix => some (.tailBound, suffix)
    | 14 :: suffix => some (.audienceTransition, suffix)
    | _ => none
  decodePrefix_encode := by intro value suffix; cases value <;> rfl

theorem stream_unknown_tag (suffix : List UInt8) :
    stream.decodePrefix (15 :: suffix) = none := rfl

/-- The signature adapter's typed rejection, named. Key absence, unusable key
records and a key version that is unregistered or revoked (its standing in the
authority cell) are `unknownKey`: the subject has no usable current key. A
moved subject-key epoch, a signed footprint whose authority read has changed,
and a plan past its signed `validUntil` height are `staleRoot`: the signed plan
no longer describes the current state. A footprint that does not decode is
`malformed`; every envelope and binding failure is `badSignature`, as is a
signature the Receiver did not vouch for (`unvouched`). -/
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
  | .unvouched => .badSignature

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
(`read` 1, `write` 2, `delegate` 3, `install` 4, `revoke` 5, `append` 7, `place` 10: the tags
`request/verb` carries, the same table as the shell's `VERBS` in `shell/law.rs`); any other slot is `slot "…"`. `sealed` is `any []`, `open` is `all []`;
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
  | 7 => "append"
  | 10 => "place"
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
  | .hashEq vs b c =>
      s!"{renderSlot c} opens ({", ".intercalate (vs.map renderSlot)}) with {renderSlot b}"
  | .ran program => s!"ran {program}"
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

/-- An out-of-range order clause: where it sits in the law (`clause` is the index of
the law's top-level clause, `atom` the rest of the path), the atom as written, and the
two integers it compares (`before` holds the left operand, `after` the right one, with
`leSlotsOff`'s offset added). -/
def renderRange (leaf : LawLeaf) : String :=
  let place := match leaf.path with
    | [] => "the law"
    | [k] => s!"clause {k}"
    | k :: atom => s!"clause {k} atom {atom}"
  s!"{place}: {renderClause leaf.clause} (left {shown leaf.before}, right {shown leaf.after})"

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

/-- The room verbs read back by name, in the spelling the shell law grammar parses
(`verb == place`, `verb == append`); an unnamed tag still prints as its number. -/
theorem sample_room_verbs_rendered_compiled :
    renderClause (Pred.all [.eq "request/verb" 10, .eq "request/verb" 7,
        .memberOf "request/verb" [7, 10], .eq "request/verb" 6]) =
      "all [ verb == place, verb == append, verb in {append,place}, verb == 6 ]" := by
  native_decide

/-! ### What a field-narrowed requester is told (FIX-DISCLOSE)

A grant may name the fields it reads (`Scope.fields`, K-FIELDS). The law of a cell is
readable whole by whoever may observe the cell (the policy view is not narrowed), but which
clause of it fails, and the values its slot holds, are facts about the cell's state. So a
requester is told a clause only when the clause reads nothing outside its grant, and a value
only of a slot its grant covers:

* `slotCovered fields s`: every slot under `fields = none`; under a named set, the request's
  own coordinates (`request/…`, `target/policyId`, `context/bytes/…`, `command/bytes/…`), the
  public clock (`clock/now`), `resource/field/N/…` for a named `slot N`,
  `resource/pair/A/B/delta` for two named slots, `account/balance/A` for a named `balance A`,
  and nothing else (whole-cell bytes, content, stream and run slots are uncovered).
* `narrowed fields law old new`: under `fields = none` the full leaf (`of`); otherwise the
  first top-level conjunct of the law that reads only covered slots and fails, at its own
  first failing leaf, with a value shown only for a covered slot. `none` when no such conjunct
  fails: the refusal then names no clause (`Refusal.lawDeniedOutsideGrant`).

`narrowed_congr`: two steps that agree on every covered slot give the same narrowed leaf.
What it does not hide is the refusal's occurrence: whether the law accepts reads the whole
cell, so each refused draft still tells the requester one bit (this law rejects this step). -/

/-- The slots a requester whose grant names `fields` may be shown. -/
def slotCovered (fields : Option (Finset CellField)) (slot : Slot) : Bool :=
  match fields with
  | none => true
  | some named =>
      match slot.splitOn "/" with
      | "request" :: _ => true
      | ["target", "policyId"] => true
      | "context" :: "bytes" :: _ => true
      | "command" :: "bytes" :: _ => true
      | ["clock", "now"] => true
      | ["resource", "field", n, _] =>
          match n.toNat? with
          | some k => decide (CellField.slot k ∈ named)
          | none => false
      | ["resource", "pair", a, b, "delta"] =>
          match a.toNat?, b.toNat? with
          | some i, some j => decide (CellField.slot i ∈ named) && decide (CellField.slot j ∈ named)
          | _, _ => false
      | ["account", "balance", a] =>
          match a.toNat? with
          | some k => decide (CellField.balance k ∈ named)
          | none => false
      | _ => false

theorem slotCovered_none (slot : Slot) : slotCovered none slot = true := rfl

mutual
/-- `p` reads only slots `covered` accepts. A `witnessed` leaf reads no slot: first-party
evaluation fails it closed. -/
def readsOnly (covered : Slot → Bool) : Pred → Bool
  | .eq s _ | .le s _ | .memberOf s _ | .writeOnce s | .monotone s => covered s
  | .eqSlots a b | .leSlots a b | .leSlotsOff a b _ => covered a && covered b
  | .witnessed _ => true
  | .hashEq vs b c => covered hashEqCellSlot && vs.all covered && covered b && covered c
  | .ran program => covered (ranSlot program)
  | .not q => readsOnly covered q
  | .allL ps => readsOnlyList covered ps
  | .anyL ps => readsOnlyList covered ps
def readsOnlyList (covered : Slot → Bool) : PredList → Bool
  | .nil => true
  | .cons q rest => readsOnly covered q && readsOnlyList covered rest
end

mutual
theorem readsOnly_all : (p : Pred) → readsOnly (fun _ => true) p = true
  | .eq _ _ | .le _ _ | .memberOf _ _ | .writeOnce _ | .monotone _ | .eqSlots _ _
  | .leSlots _ _ | .leSlotsOff _ _ _ | .witnessed _ | .hashEq _ _ _ | .ran _ => by
      simp [readsOnly, List.all_eq_true]
  | .not q => by simpa [readsOnly] using readsOnly_all q
  | .allL ps => by simpa [readsOnly] using readsOnlyList_all ps
  | .anyL ps => by simpa [readsOnly] using readsOnlyList_all ps
theorem readsOnlyList_all : (ps : PredList) → readsOnlyList (fun _ => true) ps = true
  | .nil => rfl
  | .cons q rest => by
      simp only [readsOnlyList, readsOnly_all q, readsOnlyList_all rest, Bool.and_self]
end

/-- Two states agree on the slots `covered` accepts. -/
def Agree (covered : Slot → Bool) (a b : State) : Prop :=
  ∀ s, covered s = true → a.get s = b.get s

section Congr

variable {covered : Slot → Bool} {o₁ n₁ o₂ n₂ : State}

/-- Agreement on every covered slot preserves an ordered read of covered values. -/
theorem getAll_congr {a b : State} (h : Agree covered a b) :
    (slots : List Slot) → slots.all covered = true → a.getAll slots = b.getAll slots
  | [], _ => rfl
  | s :: slots, hs => by
      simp only [List.all_cons, Bool.and_eq_true] at hs
      simp only [State.getAll, h s hs.1, getAll_congr h slots hs.2]

mutual
/-- First-party evaluation of a predicate reading only covered slots is a function of
those slots. -/
theorem evalWith_congr (ho : Agree covered o₁ o₂) (hn : Agree covered n₁ n₂) :
    (p : Pred) → readsOnly covered p = true →
      evalWith failClosed p o₁ n₁ = evalWith failClosed p o₂ n₂
  | .eq s _, h | .le s _, h | .memberOf s _, h => by
      simp only [readsOnly] at h
      simp only [evalWith, hn _ h]
  | .ran program, h => by
      simp only [readsOnly] at h
      simp only [evalWith, hn _ h]
  | .writeOnce s, h | .monotone s, h => by
      simp only [readsOnly] at h
      simp only [evalWith, ho _ h, hn _ h]
  | .eqSlots a b, h | .leSlots a b, h | .leSlotsOff a b _, h => by
      simp only [readsOnly, Bool.and_eq_true] at h
      simp only [evalWith, hn _ h.1, hn _ h.2]
  | .witnessed _, _ => rfl
  | .hashEq vs b c, h => by
      simp only [readsOnly, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hc, hv⟩, hb⟩, hk⟩ := h
      simp only [evalWith, hashEqHolds, hashEqOpening, hn _ hc,
        getAll_congr hn vs hv, hn _ hb, hn _ hk]
  | .not q, h => by
      simp only [readsOnly] at h
      simp only [evalWith, evalWith_congr ho hn q h]
  | .allL ps, h => by
      simp only [readsOnly] at h
      simp only [evalWith]
      exact evalWithAll_congr ho hn ps h
  | .anyL ps, h => by
      simp only [readsOnly] at h
      simp only [evalWith]
      exact evalWithAny_congr ho hn ps h
theorem evalWithAll_congr (ho : Agree covered o₁ o₂) (hn : Agree covered n₁ n₂) :
    (ps : PredList) → readsOnlyList covered ps = true →
      evalWithAll failClosed ps o₁ n₁ = evalWithAll failClosed ps o₂ n₂
  | .nil, _ => rfl
  | .cons q rest, h => by
      simp only [readsOnlyList, Bool.and_eq_true] at h
      simp only [evalWithAll, evalWith_congr ho hn q h.1, evalWithAll_congr ho hn rest h.2]
theorem evalWithAny_congr (ho : Agree covered o₁ o₂) (hn : Agree covered n₁ n₂) :
    (ps : PredList) → readsOnlyList covered ps = true →
      evalWithAny failClosed ps o₁ n₁ = evalWithAny failClosed ps o₂ n₂
  | .nil, _ => rfl
  | .cons q rest, h => by
      simp only [readsOnlyList, Bool.and_eq_true] at h
      simp only [evalWithAny, evalWith_congr ho hn q h.1, evalWithAny_congr ho hn rest h.2]
end

mutual
/-- The first failing leaf of a predicate reading only covered slots is a function of
those slots. -/
theorem leafWith_congr (ho : Agree covered o₁ o₂) (hn : Agree covered n₁ n₂) :
    (p : Pred) → readsOnly covered p = true →
      leafWith failClosed p o₁ n₁ = leafWith failClosed p o₂ n₂
  | .allL ps, h => by
      simp only [readsOnly] at h
      simp only [leafWith]
      exact leafWithAll_congr ho hn ps h
  | .eq _ _, h | .le _ _, h | .memberOf _ _, h | .writeOnce _, h | .monotone _, h
  | .witnessed _, h | .eqSlots _ _, h | .leSlots _ _, h | .leSlotsOff _ _ _, h
  | .hashEq _ _ _, h | .ran _, h | .not _, h | .anyL _, h => by
      simp only [leafWith]
      rw [evalWith_congr ho hn _ h]
theorem leafWithAll_congr (ho : Agree covered o₁ o₂) (hn : Agree covered n₁ n₂) :
    (ps : PredList) → readsOnlyList covered ps = true →
      leafWithAll failClosed ps o₁ n₁ = leafWithAll failClosed ps o₂ n₂
  | .nil, _ => rfl
  | .cons q rest, h => by
      simp only [readsOnlyList, Bool.and_eq_true] at h
      simp only [leafWithAll]
      rw [leafWith_congr ho hn q h.1, leafWithAll_congr ho hn rest h.2]
end

theorem firstFailingLeaf_congr (ho : Agree covered o₁ o₂) (hn : Agree covered n₁ n₂)
    (p : Pred) (h : readsOnly covered p = true) :
    firstFailingLeaf p o₁ n₁ = firstFailingLeaf p o₂ n₂ :=
  leafWith_congr ho hn p h

end Congr

/-- The first conjunct from position `i` on that reads only covered slots and fails, as a
path into the conjunction. -/
def coveredFailing (covered : Slot → Bool) (old new : State) : Nat → List Pred → Option (List Nat)
  | _, [] => none
  | i, q :: rest =>
      if readsOnly covered q then
        match firstFailingLeaf q old new with
        | some path => some (i :: path)
        | none => coveredFailing covered old new (i + 1) rest
      else coveredFailing covered old new (i + 1) rest

/-- The path a requester reading `covered` is told: the first covered failing conjunct of
a conjunction, or a whole covered law's own failing leaf. -/
def coveredPath (covered : Slot → Bool) (law : Pred) (old new : State) : Option (List Nat) :=
  match law with
  | .allL ps => coveredFailing covered old new 0 ps.toList
  | _ => if readsOnly covered law then firstFailingLeaf law old new else none

/-- The leaf a requester whose grant names `fields` is told. -/
def narrowed (fields : Option (Finset CellField)) (law : Pred) (old new : State) :
    Option LawLeaf :=
  match fields with
  | none => of law old new
  | some _ => do
      let covered := slotCovered fields
      let path ← coveredPath covered law old new
      let clause ← law.subterm path
      let slot := (slotOf (explained clause)).filter covered
      pure ⟨path, clause, slot.bind old.get, slot.bind new.get⟩

/-- An unnarrowed grant is told the whole explanation. -/
theorem narrowed_none (law : Pred) (old new : State) : narrowed none law old new = of law old new :=
  rfl

theorem coveredFailing_congr {covered : Slot → Bool} {o₁ n₁ o₂ n₂ : State}
    (ho : Agree covered o₁ o₂) (hn : Agree covered n₁ n₂) :
    (i : Nat) → (qs : List Pred) →
      coveredFailing covered o₁ n₁ i qs = coveredFailing covered o₂ n₂ i qs
  | _, [] => rfl
  | i, q :: rest => by
      unfold coveredFailing
      cases reads : readsOnly covered q with
      | false => simp only [Bool.false_eq_true, if_false]; exact coveredFailing_congr ho hn (i + 1) rest
      | true =>
          simp only [if_true]
          rw [firstFailingLeaf_congr ho hn q reads, coveredFailing_congr ho hn (i + 1) rest]

theorem coveredPath_congr {covered : Slot → Bool} {o₁ n₁ o₂ n₂ : State}
    (ho : Agree covered o₁ o₂) (hn : Agree covered n₁ n₂) (law : Pred) :
    coveredPath covered law o₁ n₁ = coveredPath covered law o₂ n₂ := by
  cases law with
  | allL ps => exact coveredFailing_congr ho hn 0 ps.toList
  | _ =>
      simp only [coveredPath]
      split
      · next reads => exact firstFailingLeaf_congr ho hn _ reads
      · rfl

theorem of_congr {o₁ n₁ o₂ n₂ : State} (ho : ∀ s, o₁.get s = o₂.get s)
    (hn : ∀ s, n₁.get s = n₂.get s) (law : Pred) : of law o₁ n₁ = of law o₂ n₂ := by
  have path := firstFailingLeaf_congr (covered := fun _ => true) (fun s _ => ho s)
    (fun s _ => hn s) law (readsOnly_all law)
  have og : o₁.get = o₂.get := funext ho
  have ng : n₁.get = n₂.get := funext hn
  unfold of
  rw [path, og, ng]

/-- **The narrowed leaf depends only on the covered slots.** Two steps that agree on every
slot the grant covers give the same leaf, so the requester is told nothing about a slot
outside its grant through which clause is named or which values are shown. -/
theorem narrowed_congr (fields : Option (Finset CellField)) (law : Pred) {o₁ n₁ o₂ n₂ : State}
    (ho : Agree (slotCovered fields) o₁ o₂) (hn : Agree (slotCovered fields) n₁ n₂) :
    narrowed fields law o₁ n₁ = narrowed fields law o₂ n₂ := by
  cases fields with
  | none => exact of_congr (fun s => ho s rfl) (fun s => hn s rfl) law
  | some named =>
      simp only [narrowed]
      rw [coveredPath_congr ho hn law]
      cases coveredPath (slotCovered (some named)) law o₂ n₂ with
      | none => rfl
      | some path =>
          simp only [Option.bind_eq_bind, Option.bind_some]
          cases law.subterm path with
          | none => rfl
          | some clause =>
              simp only [Option.bind_some]
              cases slotted : (slotOf (explained clause)).filter (slotCovered (some named)) with
              | none => rfl
              | some s =>
                  have kept : slotCovered (some named) s = true := by
                    have := Option.mem_filter_iff.mp slotted
                    exact this.2
                  simp only [Option.bind_some, ho s kept, hn s kept]

/-- The named clause of a narrowed leaf is a leaf of the law, at its path, false on the step. -/
theorem coveredFailing_sound {covered : Slot → Bool} {old new : State} :
    (i : Nat) → (qs : List Pred) → (path : List Nat) →
      coveredFailing covered old new i qs = some path →
      ∃ j sub q, path = (i + j) :: sub ∧ qs[j]? = some q ∧ firstFailingLeaf q old new = some sub
  | _, [], _, h => by simp [coveredFailing] at h
  | i, q :: rest, path, h => by
      unfold coveredFailing at h
      split at h
      · cases found : firstFailingLeaf q old new with
        | some sub =>
            rw [found] at h
            cases h
            exact ⟨0, sub, q, by simp, rfl, found⟩
        | none =>
            rw [found] at h
            obtain ⟨j, sub, q', rfl, at_, fails⟩ := coveredFailing_sound (i + 1) rest path h
            exact ⟨j + 1, sub, q', by simp [Nat.add_assoc, Nat.add_comm 1 j], by simpa using at_, fails⟩
      · obtain ⟨j, sub, q', rfl, at_, fails⟩ := coveredFailing_sound (i + 1) rest path h
        exact ⟨j + 1, sub, q', by simp [Nat.add_assoc, Nat.add_comm 1 j], by simpa using at_, fails⟩

theorem subterm_toList : (ps : PredList) → (j : Nat) → (q : Pred) → (rest : List Nat) →
    ps.toList[j]? = some q → PredList.subterm ps j rest = q.subterm rest
  | .nil, _, _, _, h => by simp [PredList.toList] at h
  | .cons p _, 0, q, rest, h => by
      simp [PredList.toList] at h
      subst h
      simp [PredList.subterm]
  | .cons _ ps, j + 1, q, rest, h => by
      simp only [PredList.toList, List.getElem?_cons_succ] at h
      simp only [PredList.subterm]
      exact subterm_toList ps j q rest h

theorem narrowed_fails (fields : Option (Finset CellField)) (law : Pred) (old new : State)
    (leaf : LawLeaf) (named : narrowed fields law old new = some leaf) :
    law.subterm leaf.path = some leaf.clause ∧ leaf.clause.isLeaf = true ∧
      Minidregg.Pred.eval leaf.clause old new = false := by
  cases fields with
  | none => exact of_fails law old new leaf named
  | some covered =>
      simp only [narrowed] at named
      cases pathFound : coveredPath (slotCovered (some covered)) law old new with
      | none => simp [pathFound] at named
      | some path =>
          cases clauseFound : law.subterm path with
          | none => simp [pathFound, clauseFound] at named
          | some clause =>
              simp only [pathFound, clauseFound, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.some.injEq] at named
              subst named
              refine ⟨clauseFound, ?_⟩
              -- the clause is the failing leaf the walk named
              cases law with
              | allL ps =>
                  obtain ⟨j, sub, q, rfl, at_, fails⟩ := coveredFailing_sound 0 ps.toList path pathFound
                  obtain ⟨leafClause, sub_at, isLeaf, rejects⟩ := firstFailingLeaf_some_leaf q old new sub fails
                  have same : (Pred.allL ps).subterm ((0 + j) :: sub) = q.subterm sub := by
                    simp only [Nat.zero_add, Pred.subterm]
                    exact subterm_toList ps j q sub at_
                  rw [same, sub_at] at clauseFound
                  cases clauseFound
                  exact ⟨isLeaf, rejects⟩
              | _ =>
                  simp only [coveredPath] at pathFound
                  split at pathFound
                  · obtain ⟨leafClause, sub_at, isLeaf, rejects⟩ :=
                      firstFailingLeaf_some_leaf _ old new path pathFound
                    rw [sub_at] at clauseFound
                    cases clauseFound
                    exact ⟨isLeaf, rejects⟩
                  · cases pathFound

/-! #### The three poles, on the audit's `vault`

`vault` has field 2 = 4242 under `any [ not (verb == write), field 2 <= 3 ]`; bob's grant
names field 1 only and he prepares a write of field 1. -/

namespace NarrowSample

def vaultLaw : Pred := Pred.any [.not (.eq "request/verb" 2), .le "resource/field/2/after" 3]

/-- Bob's write of field 1 to `one`, on a vault whose field 2 holds `two`. -/
def write (one two : Int) : State :=
  ⟨[("request/verb", 2), ("resource/field/1/after", one), ("resource/field/2/after", two)]⟩

def bobFields : Option (Finset CellField) := some {CellField.slot 1}

/-- The refuting pole, on the old renderer: two vaults differing only in field 2 give
different refusals, each carrying field 2's value. -/
theorem old_leaf_discloses_uncovered :
    of vaultLaw (write 1 4242) (write 1 4242) = some ⟨[], vaultLaw, some 4242, some 4242⟩ ∧
      of vaultLaw (write 1 4242) (write 1 4242) ≠ of vaultLaw (write 1 5) (write 1 5) := by
  decide

/-- The new renderer names no clause to bob: the law reads field 2. -/
theorem narrowed_hides_uncovered_compiled :
    narrowed bobFields vaultLaw (write 1 4242) (write 1 4242) = none ∧
      narrowed bobFields vaultLaw (write 1 5) (write 1 5) = none := by
  native_decide

def fieldOneLaw : Pred :=
  Pred.all [Pred.any [.not (.eq "request/verb" 2), .le "resource/field/1/after" 3],
    Pred.any [.not (.eq "request/verb" 2), .le "resource/field/2/after" 3]]

/-- The accepting pole: a clause over a covered field is still named, with its value,
whatever the uncovered field holds. -/
theorem narrowed_shows_covered_compiled :
    narrowed bobFields fieldOneLaw (write 7 4242) (write 7 4242) =
      some ⟨[0], Pred.any [.not (.eq "request/verb" 2), .le "resource/field/1/after" 3],
        some 7, some 7⟩ ∧
    narrowed bobFields fieldOneLaw (write 7 1) (write 7 1) =
      narrowed bobFields fieldOneLaw (write 7 4242) (write 7 4242) := by
  native_decide

/-- An owner (an unnarrowed grant) is told the clause and the value, as before. -/
theorem owner_told_value :
    narrowed none vaultLaw (write 1 4242) (write 1 4242) =
      some ⟨[], vaultLaw, some 4242, some 4242⟩ := by
  decide

end NarrowSample

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

/-- An out-of-range order clause, named with its two values. -/
def Refusal.lawInputRange (leaf : LawLeaf) : Refusal :=
  ⟨.lawInputRange, RefusalReason.lawInputRange.describe, some leaf⟩

/-- The text a refusal's leaf is explained by: the out-of-range rendering for
`lawInputRange`, the failing-clause rendering otherwise. -/
def LawLeaf.explain (reason : RefusalReason) (leaf : LawLeaf) : String :=
  if reason = .lawInputRange then leaf.renderRange else leaf.render

/-- A law refusal to a requester whose grant does not cover any failing clause: the law
denies, and no clause, path or value is named (FIX-DISCLOSE). -/
def Refusal.lawDeniedOutsideGrant : Refusal :=
  ⟨.lawDenied, "a clause of the law over fields outside your grant denies this operation", none⟩

/-- An out-of-range clause is disclosed only when every slot it reads is covered.
Otherwise its path and operand values remain hidden with the generic law refusal. -/
def Refusal.lawInputRangeFor (fields : Option (Finset CellField)) (leaf : LawLeaf) : Refusal :=
  if LawLeaf.readsOnly (LawLeaf.slotCovered fields) leaf.clause then
    Refusal.lawInputRange leaf
  else Refusal.lawDeniedOutsideGrant

/-- An uncovered range diagnostic discloses neither its clause nor its operand values. -/
theorem lawInputRangeFor_hidden (fields : Option (Finset CellField)) (leaf : LawLeaf)
    (hidden : LawLeaf.readsOnly (LawLeaf.slotCovered fields) leaf.clause = false) :
    Refusal.lawInputRangeFor fields leaf = Refusal.lawDeniedOutsideGrant := by
  simp [Refusal.lawInputRangeFor, hidden]

/-- An unnarrowed grant retains the exact range diagnostic. -/
theorem lawInputRangeFor_none (leaf : LawLeaf) :
    Refusal.lawInputRangeFor none leaf = Refusal.lawInputRange leaf := by
  have covered : LawLeaf.slotCovered none = (fun _ => true) := by
    funext slot
    rfl
  simp [Refusal.lawInputRangeFor, covered, LawLeaf.readsOnly_all]

/-- The law refusal told to a requester whose grant names `fields`: the narrowed leaf
(`LawLeaf.narrowed`), or no clause when every failing clause reads outside the grant. -/
def Refusal.lawDeniedFor (fields : Option (Finset CellField)) (law : Minidregg.Pred.Pred)
    (old new : Minidregg.Pred.State) : Refusal :=
  match LawLeaf.narrowed fields law old new with
  | some leaf => Refusal.lawDenied (some leaf)
  | none => Refusal.lawDeniedOutsideGrant

/-- **`refusal_leaf_depends_only_on_covered_fields`.** Two steps that agree on every slot
the requester's grant covers give the same refusal, field for field (hence the same
refusal frame bytes). With `fields = some {slot 1}`, two vaults that differ only in field 2
are refused identically (`LawLeaf.NarrowSample`). -/
theorem refusal_leaf_depends_only_on_covered_fields (fields : Option (Finset CellField))
    (law : Minidregg.Pred.Pred) {o₁ n₁ o₂ n₂ : Minidregg.Pred.State}
    (ho : LawLeaf.Agree (LawLeaf.slotCovered fields) o₁ o₂)
    (hn : LawLeaf.Agree (LawLeaf.slotCovered fields) n₁ n₂) :
    Refusal.lawDeniedFor fields law o₁ n₁ = Refusal.lawDeniedFor fields law o₂ n₂ := by
  unfold Refusal.lawDeniedFor
  rw [LawLeaf.narrowed_congr fields law ho hn]

/-- An unnarrowed grant is told what it was told before. -/
theorem lawDeniedFor_none (law : Minidregg.Pred.Pred) (old new : Minidregg.Pred.State)
    (refused : Minidregg.Pred.eval law old new = false) :
    Refusal.lawDeniedFor none law old new = Refusal.lawDenied (LawLeaf.of law old new) := by
  unfold Refusal.lawDeniedFor
  rw [LawLeaf.narrowed_none]
  cases named : LawLeaf.of law old new with
  | some leaf => rfl
  | none =>
      have := (LawLeaf.of_none_iff law old new).mp named
      rw [refused] at this
      cases this

/-- A clause a narrowed refusal names is a leaf of the law, false on the step. -/
theorem lawDeniedFor_fails (fields : Option (Finset CellField)) (law : Minidregg.Pred.Pred)
    (old new : Minidregg.Pred.State) (leaf : LawLeaf)
    (named : Refusal.lawDeniedFor fields law old new = Refusal.lawDenied (some leaf)) :
    law.subterm leaf.path = some leaf.clause ∧ leaf.clause.isLeaf = true ∧
      Minidregg.Pred.eval leaf.clause old new = false := by
  unfold Refusal.lawDeniedFor at named
  cases found : LawLeaf.narrowed fields law old new with
  | none =>
      rw [found] at named
      simp [Refusal.lawDeniedOutsideGrant, Refusal.lawDenied] at named
  | some told =>
      rw [found] at named
      simp only [Refusal.lawDenied, Refusal.mk.injEq, Option.some.injEq, true_and] at named
      subst named
      exact LawLeaf.narrowed_fails fields law old new told found

instance : ToString Refusal := ⟨fun refusal => match refusal.leaf with
  | some leaf => s!"refused: {refusal.reason.name}: {leaf.explain refusal.reason}"
  | none => s!"refused: {refusal.reason.name}: {refusal.detail}"⟩

end Minidregg.Compiler

/-- info: 'Minidregg.Compiler.RefusalReason.capabilityRefusal_eq_none_iff_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.RefusalReason.capabilityRefusal_eq_none_iff_admissible
/-- info: 'Minidregg.Compiler.RefusalReason.sample_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.RefusalReason.sample_admitted
/-- info: 'Minidregg.Compiler.RefusalReason.sample_revoked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.RefusalReason.sample_revoked

/-- info: 'Minidregg.Compiler.LawLeaf.of_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Minidregg.Compiler.LawLeaf.of_fails

/-- info: 'Minidregg.Compiler.LawLeaf.of_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Minidregg.Compiler.LawLeaf.of_none_iff

/-- info: 'Minidregg.Compiler.refusal_leaf_depends_only_on_covered_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.refusal_leaf_depends_only_on_covered_fields

/-- info: 'Minidregg.Compiler.lawDeniedFor_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.lawDeniedFor_fails

/-- info: 'Minidregg.Compiler.LawLeaf.NarrowSample.old_leaf_discloses_uncovered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Minidregg.Compiler.LawLeaf.NarrowSample.old_leaf_discloses_uncovered
