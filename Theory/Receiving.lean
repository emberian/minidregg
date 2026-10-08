/-
# Theory.Receiving -- one receiving pipeline, its laws proved once

Every native receiver on Mini does the same five things: decode signed bytes,
recognise an exact retry in the journal, authenticate the signatures the command
names, prepare the gate-checked per-cell patch, and append one durable intent by
compare-and-swap.  Until this module each receiving family retyped that skeleton
(`Reject`, `Accepted`, `Result`, `Prepared`, `receiveLoaded`, `replay`,
`readGuards_readonly`, `requireSome`), and most of them prepared -- re-executed
-- before they verified a signature (`docs/design/RECEIVER.md`, the census).

Here the skeleton is one definition over an abstract journal (`Journal`), an
arbitrary monad and the receiver's verifier.  `Kernel.Receiving` instantiates
the journal with the deployed durable layer and the verifier with the pinned
native oracle, and runs `receive` in `IO`; the theorems below are about that
same definition, read at `Id` where a statement needs the verifier's verdicts.

**The verifier's verdicts reach `prepare` as a token** (`Vouchers`).  A
receiver is indexed by its verifier; `admitVia` runs the verifier on every claim
before `prepare` and hands `prepare` the claims it accepted, as a `Vouchers`
value of that verifier.  `Vouchers` has a private constructor: no family can
build one, and one minted under another verifier has another type.  So a gate
that needs "this key signed this message" (a capability-mode authorization, a
key rotation's possession proof) reads it from the Receiver's verdict, as a
value, instead of assuming it and having a theorem re-derive it afterwards.

* `admit_signature_first` -- an ingress one of whose signature claims the
  vouchers do not cover is refused `unauthenticated`, with a refusal computed
  from the claims and the vouchers alone: neither `prepare` (the gate, the
  re-execution) nor the shape check is consulted.  Every receiver, any `prepare`.
* `admit_ok_iff` -- admission is exactly: the claims resolve, every claim is
  vouched for, preparation (given those vouchers) succeeds, the shape check
  passes, and the written cells' laws raise no fault.
* `admitVia_vouchers_verified`, `admitVia_claims_verified` -- the vouchers
  `admitVia` mints hold only claims the verifier accepted, so an admitted
  ingress had every claim verified; `admitVia_unauthenticated` -- a claim the
  verifier refuses refuses the ingress before preparation.
* `receive_committed_prepared_verified` -- the `prepare` call behind a committed
  outcome was handed vouchers every claim of which the verifier accepted: a gate
  never holds a token the verifier did not issue.
* `guardsOff_readonly`, `guardsOff_complete` -- read guards are never on a
  written cell, and no guard on an unwritten cell is dropped.
* `replay_only_original`, `replay_after_install` -- a retry is confirmed only by
  the journal record of the same transaction with the same event and
  nullifiers, and the record live admission installs is exactly one replay
  confirms (replay = live admission).
* `receive_committed` -- a committed outcome of `receive` is an admission by
  `admitVia` over the receiver's verifier, followed by the append.
-/
import Theory.AssertAxioms

namespace Minidregg.Theory.Receiving

set_option autoImplicit false

/-! ## Signature claims and the verdict oracle -/

/-- The signature scheme a query is checked under: Ed25519 over the message
itself, or an OpenSSH `SSHSIG` signature under a namespace (the signed data is
`SSHSIG ‖ namespace ‖ … ‖ H(message)`, so a signature under one namespace never
verifies under another). -/
inductive Scheme where
  | ed25519
  | sshsig (nameSpace : List UInt8)
  deriving DecidableEq, Repr

/-- One signature obligation: the scheme, the exact key, the exact signed
message, and the presented signature.  A receiver names these from the decoded
ingress and, for keys held in state, a key lookup; never from preparation. -/
structure SigQuery where
  scheme : Scheme
  publicKey : List UInt8
  message : List UInt8
  signature : List UInt8
  deriving DecidableEq, Repr

/-- The first claim the oracle does not vouch for. -/
def firstRefused (ok : SigQuery → Bool) (claims : List SigQuery) : Option SigQuery :=
  claims.find? fun claim => !ok claim

theorem firstRefused_none_iff (ok : SigQuery → Bool) (claims : List SigQuery) :
    firstRefused ok claims = none ↔ ∀ claim ∈ claims, ok claim = true := by
  simp [firstRefused, List.find?_eq_none]

theorem firstRefused_some {ok : SigQuery → Bool} {claims : List SigQuery} {claim : SigQuery}
    (found : firstRefused ok claims = some claim) : claim ∈ claims ∧ ok claim = false := by
  refine ⟨List.mem_of_find?_eq_some found, ?_⟩
  simpa using List.find?_some found

/-- `Option` to `Except`, the one copy (22 families each defined `requireSome`). -/
def need {ε α : Type} (reason : ε) : Option α → Except ε α
  | none => .error reason
  | some value => .ok value

/-! ## The verifier's token -/

/-- **The claims a receiver's verifier accepted**, as `prepare` receives them.
Indexed by the verifier: a value minted under one verifier is not a value of
another's type.  The constructor is private to this module and its only use is
`Receiver.admitVia`, after `verify` answered `true` on each claim
(`Receiver.verifyAll`); `Vouchers.empty` vouches for nothing.  **Layer 2** (an
oracle verdict no proof expresses): `private mk` stops names, not `by
constructor`, so the guarantee is `TokenCensus` (no constant outside this module
that can carry a value mentions the constructor; a planted forgery is detected). -/
structure Vouchers {m : Type → Type} (verify : SigQuery → m (Except String Bool)) where
  private mk ::
  verified : List SigQuery
  /-- The receiver's OBSERVED signatures, each with the verifier's answer: a
  `false` is information the family decides on (it does not refuse), an error
  refused the ingress before anything was minted. -/
  observed : List (SigQuery × Bool)

namespace Vouchers

variable {m : Type → Type} {verify : SigQuery → m (Except String Bool)}

/-- No claim vouched for: what an ingress with no claims is prepared under
(reducible: it is the value `admitVia` mints for an empty claim list). -/
abbrev empty : Vouchers verify := ⟨[], []⟩

/-- The oracle a voucher set answers: exactly its claims. -/
def vouches (vouchers : Vouchers verify) (claim : SigQuery) : Bool := decide (claim ∈ vouchers.verified)

theorem vouches_iff (vouchers : Vouchers verify) (claim : SigQuery) :
    vouchers.vouches claim = true ↔ claim ∈ vouchers.verified := by
  simp [vouches]

/-- The vouched claim under this scheme with this key and message, if any: a
gate that needs "this key signed this message" asks for it without naming the
signature bytes.  The scheme is part of the question: an `SSHSIG` voucher is no
Ed25519 signature over the message. -/
def signed? (vouchers : Vouchers verify) (scheme : Scheme) (publicKey message : List UInt8) :
    Option SigQuery :=
  vouchers.verified.find? fun claim =>
    claim.scheme == scheme && claim.publicKey == publicKey && claim.message == message

theorem signed?_some {vouchers : Vouchers verify} {scheme : Scheme} {publicKey message : List UInt8}
    {claim : SigQuery} (found : vouchers.signed? scheme publicKey message = some claim) :
    claim ∈ vouchers.verified ∧ claim.scheme = scheme ∧ claim.publicKey = publicKey ∧
      claim.message = message := by
  refine ⟨List.mem_of_find?_eq_some found, ?_⟩
  simpa [and_assoc] using List.find?_some found

theorem empty_verified : (empty : Vouchers verify).verified = [] := rfl

/-- The verifier's answer on an observed query, if the receiver observed it. -/
def answer? (vouchers : Vouchers verify) (query : SigQuery) : Option Bool :=
  (vouchers.observed.find? fun answered => answered.1 == query).map Prod.snd

theorem answer?_some {vouchers : Vouchers verify} {query : SigQuery} {answer : Bool}
    (found : vouchers.answer? query = some answer) : (query, answer) ∈ vouchers.observed := by
  unfold answer? at found
  obtain ⟨answered, hit, rfl⟩ := Option.map_eq_some_iff.1 found
  have same : answered.1 = query := by simpa using List.find?_some hit
  have member := List.mem_of_find?_eq_some hit
  obtain ⟨q, b⟩ := answered
  cases same
  exact member

end Vouchers

/-! ## The journal a receiver commits through -/

/-- What a receiver recognises in the journal under its transaction id. -/
structure Recorded (TxId Event Nullifier : Type) where
  txId : TxId
  event : Event
  nullifiers : List Nullifier
  deriving DecidableEq

/-- The durable layer, as a receiver sees it: a loaded `State` with its
journal-bearing snapshot, a journal lookup, the intent constructor, the
executor's install, and the one law receivers need of them -- an installed
intent is found under its own id with its own event and nullifiers. -/
structure Journal where
  State : Type
  Snap : Type
  snap : State → Snap
  TxId : Type
  Event : Type
  Nullifier : Type
  Payload : Type
  Intent : Type
  txIdDecEq : DecidableEq TxId
  eventDecEq : DecidableEq Event
  nullifierDecEq : DecidableEq Nullifier
  lookup : Snap → TxId → Option (Recorded TxId Event Nullifier)
  intentOf : TxId → Event → List Nullifier → Payload → Intent
  /-- The nullifiers a prepared patch spends beyond the ingress's own (a decision's
  markers, such as a birth identity's): the intent spends the ingress's nullifiers,
  then these. -/
  spent : Payload → List Nullifier
  install : Snap → Intent → Snap
  lookup_install : ∀ snap txId event nullifiers payload,
    lookup (install snap (intentOf txId event nullifiers payload)) txId =
      some ⟨txId, event, nullifiers ++ spent payload⟩

instance (J : Journal) : DecidableEq J.TxId := J.txIdDecEq
instance (J : Journal) : DecidableEq J.Event := J.eventDecEq
instance (J : Journal) : DecidableEq J.Nullifier := J.nullifierDecEq

/-! ## The receiver declaration -/

/-- One receiving family under the verifier `verify`: its codec, its command,
the signature claims it makes, its gate and per-cell patch (`prepare`, given the
verifier's vouchers; `payload`), its shape check, and its journal identity
(`txId`, `event`, `nullifiers`).  Everything else -- the order of the steps, the
refusal type, the accepted object, replay, the outcome -- is defined once below. -/
structure Receiver (J : Journal) {m : Type → Type} (verify : SigQuery → m (Except String Bool)) where
  Env : Type
  Ingress : Type
  Command : Type
  Reject : Type
  Prepared : Env → J.State → Command → Type
  decode : List UInt8 → Option Ingress
  command : Ingress → Command
  /-- The signature claims: from the decoded ingress and a key lookup.  Each must
  verify, or the ingress is refused `unauthenticated`. -/
  claims : Env → J.State → Ingress → Except Reject (List SigQuery)
  /-- The OBSERVED signatures: checked by the same verifier before `prepare`, whose
  true/false answers reach `prepare` (`Vouchers.answer?`) for the family to decide
  on.  A verifier error refuses; a `false` does not. -/
  observations : Env → J.State → Ingress → Except Reject (List SigQuery)
  /-- The gate and the patch: the only step that may re-execute anything.  It
  receives the claims the verifier accepted, and nothing else about signatures. -/
  prepare : Vouchers verify → (env : Env) → (state : J.State) → (command : Command) →
    Except Reject (Prepared env state command)
  shape : {env : Env} → {state : J.State} → {command : Command} →
    Prepared env state command → Bool
  /-- Why the laws of the written cells refuse a prepared patch. -/
  Fault : Type
  /-- The law check, after the physical shape: `none` when every written cell's
  law admits the patch, else the first fault.  A function of the prepared value
  alone, so replay and the audit walk re-derive the same verdict. -/
  lawFault : {env : Env} → {state : J.State} → {command : Command} →
    Prepared env state command → Option Fault
  txId : Env → Ingress → J.TxId
  event : Env → Ingress → J.Event
  nullifiers : Env → Ingress → List J.Nullifier
  payload : {env : Env} → {state : J.State} → (ingress : Ingress) →
    Prepared env state (command ingress) → J.Payload

variable {J : Journal}

/-- Every refusal a receiver can produce. -/
inductive Refusal (Reject Fault : Type) where
  | malformed
  | family (reason : Reject)
  | unauthenticated (claim : SigQuery)
  | verifier (detail : String)
  | shape
  /-- A written cell's law refused the patch; the receiver names why. -/
  | law (fault : Fault)
  deriving Repr

namespace Receiver

/-! ## The verifier -/

/-- Verify the claims in order, stopping at the first refusal; the result is
the claims the verifier accepted (a prefix of `claims`). -/
def verifyAll {n : Type → Type} [Monad n] (check : SigQuery → n (Except String Bool)) :
    List SigQuery → n (Except String (List SigQuery))
  | [] => pure (.ok [])
  | claim :: rest => do
      match ← check claim with
      | .error detail => pure (.error detail)
      | .ok false => pure (.ok [])
      | .ok true =>
          match ← verifyAll check rest with
          | .error detail => pure (.error detail)
          | .ok verified => pure (.ok (claim :: verified))

/-- Ask the verifier about each observed query, in order; an error stops. -/
def observeAll {n : Type → Type} [Monad n] (check : SigQuery → n (Except String Bool)) :
    List SigQuery → n (Except String (List (SigQuery × Bool)))
  | [] => pure (.ok [])
  | query :: rest => do
      match ← check query with
      | .error detail => pure (.error detail)
      | .ok answer =>
          match ← observeAll check rest with
          | .error detail => pure (.error detail)
          | .ok answered => pure (.ok ((query, answer) :: answered))

/-- The verifier that answers `v`, at `Id`. -/
def pureVerifier (v : SigQuery → Bool) : SigQuery → Id (Except String Bool) :=
  fun claim => pure (.ok (v claim))

section Generic

variable {m : Type → Type} {verify : SigQuery → m (Except String Bool)}
variable (R : Receiver J verify)

/-- What an admission asserts of a prepared patch: it was prepared under vouchers
of the receiver's verifier that cover every claim the ingress makes, and it passed
the physical shape and the written cells' laws. -/
def Admits (env : R.Env) (state : J.State) (ingress : R.Ingress)
    (prepared : R.Prepared env state (R.command ingress)) : Prop :=
  ∃ (vouchers : Vouchers verify) (claims : List SigQuery),
    R.claims env state ingress = .ok claims ∧
    (∀ claim ∈ claims, vouchers.vouches claim = true) ∧
    R.prepare vouchers env state (R.command ingress) = .ok prepared ∧
    R.shape prepared = true ∧ R.lawFault prepared = none

/-- An admitted ingress.  **Layer 1**: it carries the proposition it asserts
(`admits`), so a value built any way at all -- `admit`, a tactic, a metaprogram --
is a prepared patch that passed the gate (its proof field `admits`, which the token
census names as its layer-1 witness).  The vouchers the
proposition names are layer 2 (`Vouchers`). -/
structure Accepted (env : R.Env) (state : J.State) (ingress : R.Ingress) where
  private mk ::
  prepared : R.Prepared env state (R.command ingress)
  admits : R.Admits env state ingress prepared

/-- Admission under a voucher set: every claim must be vouched for, then
prepare (given the vouchers), then check the physical shape, then the written
cells' laws.  The order is the content of `admit_signature_first`. -/
def admit (env : R.Env) (state : J.State) (ingress : R.Ingress) (vouchers : Vouchers verify) :
    Except (Refusal R.Reject R.Fault) (R.Accepted env state ingress) :=
  match resolved : R.claims env state ingress with
  | .error reason => .error (.family reason)
  | .ok claims =>
      match refused : firstRefused vouchers.vouches claims with
      | some claim => .error (.unauthenticated claim)
      | none =>
          match preparedEq : R.prepare vouchers env state (R.command ingress) with
          | .error reason => .error (.family reason)
          | .ok prepared =>
              if shaped : R.shape prepared = true then
                match lawful : R.lawFault prepared with
                | none => .ok ⟨prepared, vouchers, claims, resolved,
                    (firstRefused_none_iff _ claims).1 refused, preparedEq, shaped, lawful⟩
                | some fault => .error (.law fault)
              else .error .shape

/-- **Signature before any re-execution.**  When a claim is not vouched for,
admission is the `unauthenticated` refusal of the first such claim -- a value
fixed by the claims and the vouchers alone.  The statement holds for every
receiver, so for every `prepare` and `shape`: neither is consulted. -/
theorem admit_signature_first {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {vouchers : Vouchers verify} {claims : List SigQuery} {claim : SigQuery}
    (resolved : R.claims env state ingress = .ok claims)
    (refused : firstRefused vouchers.vouches claims = some claim) :
    R.admit env state ingress vouchers = .error (.unauthenticated claim) := by
  unfold admit
  split
  · rename_i reason resolvedEq
    rw [resolved] at resolvedEq
    cases resolvedEq
  · rename_i claims' resolvedEq
    rw [resolved] at resolvedEq
    cases resolvedEq
    split
    · rename_i found refusedEq
      rw [refused] at refusedEq
      cases refusedEq
      rfl
    · rename_i refusedEq
      rw [refused] at refusedEq
      cases refusedEq

/-- **Admission, exactly.** -/
theorem admit_ok_iff {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {vouchers : Vouchers verify} (accepted : R.Accepted env state ingress) :
    R.admit env state ingress vouchers = .ok accepted ↔
      ∃ claims, R.claims env state ingress = .ok claims ∧
        (∀ claim ∈ claims, vouchers.vouches claim = true) ∧
        R.prepare vouchers env state (R.command ingress) = .ok accepted.prepared ∧
        R.shape accepted.prepared = true ∧ R.lawFault accepted.prepared = none := by
  obtain ⟨prepared, admits⟩ := accepted
  unfold admit
  constructor
  · intro admitted
    split at admitted
    · cases admitted
    · rename_i claims resolved
      split at admitted
      · cases admitted
      · rename_i none_refused
        split at admitted
        · cases admitted
        · rename_i prepared' preparedEq
          split at admitted
          · rename_i shaped
            split at admitted
            · rename_i lawful
              cases admitted
              exact ⟨claims, resolved, (firstRefused_none_iff _ claims).1 none_refused,
                preparedEq, shaped, lawful⟩
            · cases admitted
          · cases admitted
  · rintro ⟨claims, resolved, verified, preparedEq, shaped, lawful⟩
    have unrefused := (firstRefused_none_iff _ claims).2 verified
    split
    · rename_i reason resolvedEq
      rw [resolved] at resolvedEq
      cases resolvedEq
    · rename_i claims' resolvedEq
      rw [resolved] at resolvedEq
      cases resolvedEq
      split
      · rename_i found refusedEq
        rw [unrefused] at refusedEq
        cases refusedEq
      · split
        · rename_i reason preparedEq'
          rw [preparedEq] at preparedEq'
          cases preparedEq'
        · rename_i prepared' preparedEq'
          rw [preparedEq] at preparedEq'
          cases preparedEq'
          split
          · split
            · rfl
            · rename_i fault lawfulEq
              rw [lawful] at lawfulEq
              cases lawfulEq
          · rename_i notShaped
            exact absurd shaped notShaped

/-- **Every step passed, so admission accepts**: the accepted value carries that
patch. -/
theorem admit_ok_of {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {vouchers : Vouchers verify} {claims : List SigQuery}
    {prepared : R.Prepared env state (R.command ingress)}
    (resolved : R.claims env state ingress = .ok claims)
    (verified : ∀ claim ∈ claims, vouchers.vouches claim = true)
    (preparedEq : R.prepare vouchers env state (R.command ingress) = .ok prepared)
    (shaped : R.shape prepared = true) (lawful : R.lawFault prepared = none) :
    ∃ accepted, R.admit env state ingress vouchers = .ok accepted ∧
      accepted.prepared = prepared :=
  ⟨⟨prepared, vouchers, claims, resolved, verified, preparedEq, shaped, lawful⟩,
    (R.admit_ok_iff _).2 ⟨claims, resolved, verified, preparedEq, shaped, lawful⟩, rfl⟩

/-- **A law fault refuses**, naming the fault: a patch that prepares and passes
the physical shape but whose laws raise `fault` is refused `law fault`. -/
theorem admit_law_refused {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {vouchers : Vouchers verify} {claims : List SigQuery}
    {prepared : R.Prepared env state (R.command ingress)} {fault : R.Fault}
    (resolved : R.claims env state ingress = .ok claims)
    (verified : ∀ claim ∈ claims, vouchers.vouches claim = true)
    (preparedEq : R.prepare vouchers env state (R.command ingress) = .ok prepared)
    (shaped : R.shape prepared = true) (faulted : R.lawFault prepared = some fault) :
    R.admit env state ingress vouchers = .error (.law fault) := by
  have unrefused := (firstRefused_none_iff _ claims).2 verified
  unfold admit
  split
  · rename_i reason resolvedEq
    rw [resolved] at resolvedEq
    cases resolvedEq
  · rename_i claims' resolvedEq
    rw [resolved] at resolvedEq
    cases resolvedEq
    split
    · rename_i found refusedEq
      rw [unrefused] at refusedEq
      cases refusedEq
    · split
      · rename_i reason preparedEq'
        rw [preparedEq] at preparedEq'
        cases preparedEq'
      · rename_i prepared' preparedEq'
        rw [preparedEq] at preparedEq'
        cases preparedEq'
        split
        · split
          · rename_i lawfulEq
            rw [faulted] at lawfulEq
            cases lawfulEq
          · rename_i fault' faultEq
            rw [faulted] at faultEq
            cases faultEq
            rfl
        · rename_i notShaped
          exact absurd shaped notShaped

/-- An admission together with the vouchers it was made under. -/
structure Admitted (env : R.Env) (state : J.State) (ingress : R.Ingress) where
  vouchers : Vouchers verify
  accepted : R.Accepted env state ingress
  admitted : R.admit env state ingress vouchers = .ok accepted

/-- **Every admission is lawful**: its prepared patch passed the physical shape
and its laws raised no fault. -/
theorem Admitted.lawful {R : Receiver J verify} {env : R.Env} {state : J.State}
    {ingress : R.Ingress} (admission : R.Admitted env state ingress) :
    R.shape admission.accepted.prepared = true ∧ R.lawFault admission.accepted.prepared = none := by
  obtain ⟨-, -, -, -, -, shaped, lawful⟩ := admission.accepted.admits
  exact ⟨shaped, lawful⟩

/-- **Every admission was prepared under its own vouchers**, and each of its
claims is among them. -/
theorem Admitted.prepared {R : Receiver J verify} {env : R.Env} {state : J.State}
    {ingress : R.Ingress} (admission : R.Admitted env state ingress) :
    R.prepare admission.vouchers env state (R.command ingress) = .ok admission.accepted.prepared ∧
      ∃ claims, R.claims env state ingress = .ok claims ∧
        ∀ claim ∈ claims, claim ∈ admission.vouchers.verified := by
  obtain ⟨claims, resolved, vouched, preparedEq, -, -⟩ :=
    (R.admit_ok_iff admission.accepted).1 admission.admitted
  exact ⟨preparedEq, claims, resolved, fun claim member =>
    (Vouchers.vouches_iff _ _).1 (vouched claim member)⟩

/-- The one admission path: resolve claims, verify them with the receiver's
verifier, mint the vouchers of the accepted claims, admit.  The live receiver
and the audit walk both call this, so the walk's re-admission is the live
admission.  This is the only place a `Vouchers` value is constructed. -/
def admitVia [Monad m] (env : R.Env) (state : J.State) (ingress : R.Ingress) :
    m (Except (Refusal R.Reject R.Fault) (R.Admitted env state ingress)) := do
  match R.claims env state ingress with
  | .error reason => pure (.error (.family reason))
  | .ok claims =>
      match ← verifyAll verify claims with
      | .error detail => pure (.error (.verifier detail))
      | .ok verified =>
          match R.observations env state ingress with
          | .error reason => pure (.error (.family reason))
          | .ok queries =>
              match ← observeAll verify queries with
              | .error detail => pure (.error (.verifier detail))
              | .ok observed =>
                  match admitted : R.admit env state ingress ⟨verified, observed⟩ with
                  | .error reason => pure (.error reason)
                  | .ok accepted => pure (.ok ⟨⟨verified, observed⟩, accepted, admitted⟩)

/-! ## Read guards -/

/-- The read guards of a patch: the observed cells it does not write. -/
def guardsOff {W G C : Type} [DecidableEq C] (writeCell : W → C) (guardCell : G → C)
    (writes : List W) (guards : List G) : List G :=
  guards.filter fun guard => decide (guardCell guard ∉ writes.map writeCell)

/-- **Read guards are read-only**: no guard names a written cell. -/
theorem guardsOff_readonly {W G C : Type} [DecidableEq C] {writeCell : W → C}
    {guardCell : G → C} {writes : List W} {guards : List G} {guard : G}
    (member : guard ∈ guardsOff writeCell guardCell writes guards) :
    guardCell guard ∉ writes.map writeCell := by
  simpa [guardsOff] using (List.mem_filter.mp member).2

/-- And no guard on an unwritten cell is dropped. -/
theorem guardsOff_complete {W G C : Type} [DecidableEq C] {writeCell : W → C}
    {guardCell : G → C} {writes : List W} {guards : List G} {guard : G}
    (member : guard ∈ guards) (unwritten : guardCell guard ∉ writes.map writeCell) :
    guard ∈ guardsOff writeCell guardCell writes guards :=
  List.mem_filter.mpr ⟨member, by simpa using unwritten⟩

/-! ## The intent, replay, and the outcome -/

/-- The durable intent of an admission. -/
def intent {env : R.Env} {state : J.State} {ingress : R.Ingress}
    (accepted : R.Accepted env state ingress) : J.Intent :=
  J.intentOf (R.txId env ingress) (R.event env ingress) (R.nullifiers env ingress)
    (R.payload ingress accepted.prepared)

/-- A receipt names the transaction and its event. -/
def receipt (env : R.Env) (ingress : R.Ingress) : J.TxId × J.Event :=
  (R.txId env ingress, R.event env ingress)

/-- Exact retry: `none` when the transaction is not journaled; a receipt when
the journal holds this transaction with this event, spending this ingress's
nullifiers first (then whatever its prepared patch spent, which replay does not
re-derive); a conflict otherwise. -/
def replay (env : R.Env) (state : J.State) (ingress : R.Ingress) :
    Option (Except Unit (J.TxId × J.Event)) :=
  match J.lookup (J.snap state) (R.txId env ingress) with
  | none => none
  | some recorded =>
      if recorded.txId = R.txId env ingress ∧ recorded.event = R.event env ingress ∧
          (R.nullifiers env ingress).isPrefixOf recorded.nullifiers = true then
        some (.ok (R.receipt env ingress))
      else some (.error ())

/-- **Replay confirms only the original.** -/
theorem replay_only_original {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {selected : J.TxId × J.Event} (found : R.replay env state ingress = some (.ok selected)) :
    selected = R.receipt env ingress ∧
      ∃ rest, J.lookup (J.snap state) (R.txId env ingress) =
        some ⟨R.txId env ingress, R.event env ingress, R.nullifiers env ingress ++ rest⟩ := by
  unfold replay at found
  split at found
  · cases found
  · rename_i recorded looked
    split at found
    · rename_i exact
      cases found
      obtain ⟨txIdEq, eventEq, prefixed⟩ := exact
      obtain ⟨rest, restEq⟩ := List.isPrefixOf_iff_prefix.1 prefixed
      refine ⟨rfl, rest, looked.trans (congrArg some ?_)⟩
      obtain ⟨txId, event, nullifiers⟩ := recorded
      simp only at txIdEq eventEq restEq
      subst txIdEq eventEq restEq
      rfl
    · cases found

/-- **Replay = live admission.**  In any state whose journal snapshot installs
the intent of an admission, replaying the same ingress confirms it with the
same receipt: the record live admission writes is the one replay recognises. -/
theorem replay_after_install {env : R.Env} {state : J.State} {ingress : R.Ingress}
    (accepted : R.Accepted env state ingress) (later : J.State) (before : J.Snap)
    (installed : J.snap later = J.install before (R.intent accepted)) :
    R.replay env later ingress = some (.ok (R.receipt env ingress)) := by
  unfold replay
  rw [installed, intent, J.lookup_install]
  simp [List.isPrefixOf_iff_prefix]

/-- What one receipt attempt produced. -/
inductive Outcome (env : R.Env) (state : J.State)
    (Exact : J.State → J.Intent → Type) (Other : Type) where
  | replayed (receipt : J.TxId × J.Event)
  | conflict
  | refused (reason : Refusal R.Reject R.Fault)
  | committed (ingress : R.Ingress) (admission : R.Admitted env state ingress)
      (witness : Exact state (R.intent admission.accepted))
  | durable (ingress : R.Ingress) (outcome : Other)

end Generic

/-- One append attempt: the store's evidence that exactly this intent was
appended, or any other settlement. -/
inductive Commit (Exact : Type) (Other : Type) where
  | exact (witness : Exact)
  | other (outcome : Other)

section Pipeline

variable {m : Type → Type} {verify : SigQuery → m (Except String Bool)}
variable (R : Receiver J verify)

/-- **The receiving pipeline**, the one copy: decode, exact retry, admission
(`admitVia`: claims, the receiver's verifier, then preparation under the
vouchers), append. -/
def receive [Monad m] {Exact : J.State → J.Intent → Type} {Other : Type}
    (append : (state : J.State) → (intent : J.Intent) → m (Commit (Exact state intent) Other))
    (env : R.Env) (state : J.State) (bytes : List UInt8) :
    m (R.Outcome env state Exact Other) := do
  match R.decode bytes with
  | none => pure (.refused .malformed)
  | some ingress =>
      match R.replay env state ingress with
      | some (.ok selected) => pure (.replayed selected)
      | some (.error ()) => pure .conflict
      | none =>
          match ← R.admitVia env state ingress with
          | .error reason => pure (.refused reason)
          | .ok admission =>
              match ← append state (R.intent admission.accepted) with
              | .exact witness => pure (.committed ingress admission witness)
              | .other outcome => pure (.durable ingress outcome)

end Pipeline

/-! ## The verifier's verdicts, read at `Id` -/

section AtId

variable {verify : SigQuery → Id (Except String Bool)} (R : Receiver J verify)

/-- **A committed outcome is a fresh, admitted, appended ingress**: the bytes
decoded, the journal did not hold the transaction, `admitVia` (claims, the
verifier, then preparation) admitted it, and the append returned exactly the
witness the outcome carries. -/
theorem receive_committed {Exact : J.State → J.Intent → Type} {Other : Type}
    {append : (state : J.State) → (intent : J.Intent) → Id (Commit (Exact state intent) Other)}
    {env : R.Env} {state : J.State} {bytes : List UInt8} {ingress : R.Ingress}
    {admission : R.Admitted env state ingress} {witness : Exact state (R.intent admission.accepted)}
    (committed : R.receive append env state bytes = pure (.committed ingress admission witness)) :
    R.decode bytes = some ingress ∧ R.replay env state ingress = none ∧
      R.admitVia env state ingress = pure (.ok admission) ∧
      append state (R.intent admission.accepted) = pure (.exact witness) := by
  unfold receive at committed
  split at committed
  · cases committed
  · rename_i decoded ingress' decodedEq
    split at committed
    · cases committed
    · cases committed
    · rename_i fresh
      simp only [bind] at committed
      split at committed
      · cases committed
      · rename_i admission' admittedEq
        split at committed
        · rename_i witness' appendedEq
          cases committed
          exact ⟨decodedEq, fresh, admittedEq, appendedEq⟩
        · cases committed

/-- **A committed ingress is lawful**: the admission a committed outcome carries
passed the physical shape and raised no law fault. -/
theorem receive_committed_lawFault {Exact : J.State → J.Intent → Type} {Other : Type}
    {append : (state : J.State) → (intent : J.Intent) → Id (Commit (Exact state intent) Other)}
    {env : R.Env} {state : J.State} {bytes : List UInt8} {ingress : R.Ingress}
    {admission : R.Admitted env state ingress} {witness : Exact state (R.intent admission.accepted)}
    (_committed : R.receive append env state bytes = pure (.committed ingress admission witness)) :
    R.shape admission.accepted.prepared = true ∧ R.lawFault admission.accepted.prepared = none :=
  admission.lawful

/-- At `Id`, the verifier's accepted list holds only claims it answered `true` on. -/
theorem verifyAll_sound (verify : SigQuery → Id (Except String Bool)) :
    ∀ {claims verified : List SigQuery}, verifyAll verify claims = (pure (.ok verified) : Id _) →
      ∀ claim ∈ verified, verify claim = pure (.ok true)
  | [], verified, ran => by
      intro claim member
      have empty : (Except.ok [] : Except String (List SigQuery)) = .ok verified := ran
      cases empty
      cases member
  | head :: rest, verified, ran => by
      intro claim member
      cases verdict : verify head with
      | error detail =>
          simp [verifyAll, verdict, bind, pure] at ran
      | ok accepted =>
          cases accepted with
          | false =>
              simp [verifyAll, verdict, bind, pure] at ran
              cases ran
              cases member
          | true =>
              cases tail : verifyAll verify rest with
              | error detail => simp [verifyAll, verdict, tail, bind, pure] at ran
              | ok verifiedRest =>
                  simp [verifyAll, verdict, tail, bind, pure] at ran
                  cases ran
                  rcases List.mem_cons.mp member with same | later
                  · subst same
                    exact verdict
                  · exact verifyAll_sound verify tail claim later

/-- **A claim the verifier does not accept refuses before preparation**, under
any `Id` verifier (a recorded transcript answers an unrecorded claim with an
error, never `false`): `admitVia` returns a `verifier` or an `unauthenticated`
refusal -- never an admission, and never a refusal `prepare` produced. -/
theorem admitVia_refused_before_prepare {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {claims queries : List SigQuery} {bad : SigQuery}
    (resolved : R.claims env state ingress = .ok claims)
    (observing : R.observations env state ingress = .ok queries) (member : bad ∈ claims)
    (notAccepted : verify bad ≠ pure (.ok true)) :
    (∃ detail, R.admitVia env state ingress = (pure (.error (.verifier detail)) : Id _)) ∨
      ∃ claim ∈ claims,
        R.admitVia env state ingress = (pure (.error (.unauthenticated claim)) : Id _) := by
  unfold admitVia
  simp only [resolved]
  cases ran : verifyAll verify claims with
  | error detail => exact Or.inl ⟨detail, rfl⟩
  | ok verified =>
    simp only [observing]
    cases asked : observeAll verify queries with
    | error detail => exact Or.inl ⟨detail, by simp [bind, pure]⟩
    | ok observed =>
      have notIn : bad ∉ verified := fun mem => notAccepted (verifyAll_sound verify ran bad mem)
      have notNone : firstRefused (Vouchers.vouches (⟨verified, observed⟩ : Vouchers verify))
          claims ≠ none := by
        intro none_refused
        exact notIn ((Vouchers.vouches_iff _ _).1
          ((firstRefused_none_iff _ claims).1 none_refused bad member))
      obtain ⟨claim, found⟩ := Option.ne_none_iff_exists'.1 notNone
      obtain ⟨claimMember, -⟩ := firstRefused_some found
      refine Or.inr ⟨claim, claimMember, ?_⟩
      simp only [bind, pure, ran, asked]
      split
      · rename_i reason refusedEq
        rw [R.admit_signature_first resolved found] at refusedEq
        cases refusedEq
        rfl
      · rename_i accepted admittedEq
        rw [R.admit_signature_first resolved found] at admittedEq
        cases admittedEq

/-- At `Id`, every observed answer is the verifier's answer on exactly that
query, and every observation was answered, in order. -/
theorem observeAll_sound (verify : SigQuery → Id (Except String Bool)) :
    ∀ {queries : List SigQuery} {observed : List (SigQuery × Bool)},
      observeAll verify queries = (pure (.ok observed) : Id _) →
        observed.map Prod.fst = queries ∧ ∀ answered ∈ observed, verify answered.1 = pure (.ok answered.2)
  | [], observed, ran => by
      have empty : (Except.ok [] : Except String (List (SigQuery × Bool))) = .ok observed := ran
      cases empty
      exact ⟨rfl, fun _ member => by cases member⟩
  | head :: rest, observed, ran => by
      cases verdict : verify head with
      | error detail => simp [observeAll, verdict, bind, pure] at ran
      | ok answer =>
          cases tail : observeAll verify rest with
          | error detail => simp [observeAll, verdict, tail, bind, pure] at ran
          | ok answeredRest =>
              simp [observeAll, verdict, tail, bind, pure] at ran
              cases ran
              obtain ⟨keys, sound⟩ := observeAll_sound verify tail
              refine ⟨by simp [keys], ?_⟩
              intro answered member
              rcases List.mem_cons.mp member with same | later
              · subst same; exact verdict
              · exact sound answered later

/-- **An observed answer is the verifier's answer.**  The vouchers of an
admission `admitVia` made, under any `Id` verifier, answer exactly the
receiver's observations, in order, and each answer is what the verifier returned
on that exact query (scheme, key, message, signature).  With `Vouchers`' private
constructor, a family's `prepare` reads an observation's verdict from nowhere
else. -/
theorem admitVia_observed {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {admission : R.Admitted env state ingress}
    (admitted : R.admitVia env state ingress = (pure (.ok admission) : Id _)) :
    ∃ queries, R.observations env state ingress = .ok queries ∧
      admission.vouchers.observed.map Prod.fst = queries ∧
      ∀ answered ∈ admission.vouchers.observed, verify answered.1 = pure (.ok answered.2) := by
  unfold admitVia at admitted
  split at admitted
  · cases admitted
  · rename_i claims _
    simp only [bind] at admitted
    split at admitted
    · cases admitted
    · rename_i verified _
      split at admitted
      · cases admitted
      · rename_i queries observing
        split at admitted
        · cases admitted
        · rename_i observed asked
          split at admitted
          · cases admitted
          · cases admitted
            exact ⟨queries, observing, observeAll_sound verify asked⟩

end AtId

section PureVerdicts

variable {v : SigQuery → Bool} (R : Receiver J (pureVerifier v))

/-- At `Id`, the verifier accepts exactly the longest prefix it vouches for. -/
theorem verifyAll_pure (v : SigQuery → Bool) :
    ∀ claims : List SigQuery,
      verifyAll (pureVerifier v) claims = (pure (.ok (claims.takeWhile v)) : Id _)
  | [] => rfl
  | claim :: rest => by
      cases accepted : v claim
      · simp [verifyAll, pureVerifier, accepted]
      · have tail := verifyAll_pure v rest
        simp only [verifyAll, pureVerifier, bind, pure] at tail ⊢
        simp [accepted, tail]

/-- At `Id`, the pure verifier answers every observation with `v`. -/
theorem observeAll_pure (v : SigQuery → Bool) :
    ∀ queries : List SigQuery,
      observeAll (pureVerifier v) queries =
        (pure (.ok (queries.map fun query => (query, v query))) : Id _)
  | [] => rfl
  | query :: rest => by
      have tail := observeAll_pure v rest
      simp only [observeAll, pureVerifier, bind, pure] at tail ⊢
      simp [tail]

theorem takeWhile_vouched (v : SigQuery → Bool) :
    ∀ {claims : List SigQuery} {claim : SigQuery}, claim ∈ claims.takeWhile v → v claim = true
  | [], _, member => by simp at member
  | head :: rest, claim, member => by
      cases verdict : v head
      · simp [verdict] at member
      · simp only [List.takeWhile_cons, verdict] at member
        rcases List.mem_cons.mp member with same | later
        · exact same ▸ verdict
        · exact takeWhile_vouched v later

/-- **The vouchers hold only verified claims**: every claim in the vouchers of
an admission `admitVia` made is one the verifier accepted. -/
theorem admitVia_vouchers_verified {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {admission : R.Admitted env state ingress}
    (admitted : R.admitVia env state ingress = (pure (.ok admission) : Id _)) :
    ∀ claim ∈ admission.vouchers.verified, v claim = true := by
  unfold admitVia at admitted
  split at admitted
  · cases admitted
  · rename_i claims _
    rw [show (verifyAll (pureVerifier v) claims >>= _) = _ from
      congrArg (· >>= _) (verifyAll_pure v claims)] at admitted
    simp only [bind, pure] at admitted
    split at admitted
    · cases admitted
    · rename_i queries _
      rw [observeAll_pure v queries] at admitted
      simp only [pure] at admitted
      split at admitted
      · cases admitted
      · cases admitted
        intro claim member
        exact takeWhile_vouched v member

/-- **An admitted ingress had every claim verified.** -/
theorem admitVia_claims_verified {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {admission : R.Admitted env state ingress}
    (admitted : R.admitVia env state ingress = (pure (.ok admission) : Id _)) :
    ∃ claims, R.claims env state ingress = .ok claims ∧ ∀ claim ∈ claims, v claim = true := by
  obtain ⟨-, claims, resolved, vouched⟩ := admission.prepared
  exact ⟨claims, resolved, fun claim member =>
    R.admitVia_vouchers_verified admitted claim (vouched claim member)⟩

/-- **A refused signature refuses before preparation**, through the live path:
if the verifier refuses one of the claims, `admitVia` returns an
`unauthenticated` refusal naming one of the claims -- never an admission, and
never a `family` refusal that `prepare` could have produced. -/
theorem admitVia_unauthenticated {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {claims queries : List SigQuery} {bad : SigQuery}
    (resolved : R.claims env state ingress = .ok claims)
    (observing : R.observations env state ingress = .ok queries)
    (member : bad ∈ claims) (refused : v bad = false) :
    ∃ claim, claim ∈ claims ∧
      R.admitVia env state ingress = (pure (.error (.unauthenticated claim)) : Id _) := by
  have notNone : firstRefused
      (Vouchers.vouches (⟨claims.takeWhile v, queries.map fun query => (query, v query)⟩ :
        Vouchers (pureVerifier v))) claims ≠ none := by
    intro none_refused
    have vouched := (firstRefused_none_iff _ claims).1 none_refused bad member
    have := takeWhile_vouched v ((Vouchers.vouches_iff _ _).1 vouched)
    rw [this] at refused
    cases refused
  obtain ⟨claim, found⟩ := Option.ne_none_iff_exists'.1 notNone
  obtain ⟨claimMember, -⟩ := firstRefused_some found
  refine ⟨claim, claimMember, ?_⟩
  unfold admitVia
  simp only [resolved]
  rw [show (verifyAll (pureVerifier v) claims >>= _) = _ from
    congrArg (· >>= _) (verifyAll_pure v claims)]
  simp only [bind, pure, observing]
  rw [observeAll_pure v queries]
  simp only [pure]
  split
  · rename_i reason refusedEq
    rw [R.admit_signature_first resolved found] at refusedEq
    cases refusedEq
    rfl
  · rename_i accepted admittedEq
    rw [R.admit_signature_first resolved found] at admittedEq
    cases admittedEq

/-- At the pure verifier: a committed ingress had every claim verified. -/
theorem receive_committed_verified {Exact : J.State → J.Intent → Type} {Other : Type}
    {append : (state : J.State) → (intent : J.Intent) → Id (Commit (Exact state intent) Other)}
    {env : R.Env} {state : J.State} {bytes : List UInt8} {ingress : R.Ingress}
    {admission : R.Admitted env state ingress} {witness : Exact state (R.intent admission.accepted)}
    (committed : R.receive append env state bytes = pure (.committed ingress admission witness)) :
    ∃ claims, R.claims env state ingress = .ok claims ∧ ∀ claim ∈ claims, v claim = true :=
  R.admitVia_claims_verified (R.receive_committed committed).2.2.1

/-- **`prepare` holds only what the verifier issued.**  The `prepare` call
behind a committed outcome was handed exactly the admission's vouchers, and every
claim in them is one the verifier accepted.  With `Vouchers`' private
constructor, this is the whole of how a gate can come to hold a signature
verdict. -/
theorem receive_committed_prepared_verified {Exact : J.State → J.Intent → Type} {Other : Type}
    {append : (state : J.State) → (intent : J.Intent) → Id (Commit (Exact state intent) Other)}
    {env : R.Env} {state : J.State} {bytes : List UInt8} {ingress : R.Ingress}
    {admission : R.Admitted env state ingress} {witness : Exact state (R.intent admission.accepted)}
    (committed : R.receive append env state bytes = pure (.committed ingress admission witness)) :
    R.prepare admission.vouchers env state (R.command ingress) = .ok admission.accepted.prepared ∧
      ∀ claim ∈ admission.vouchers.verified, v claim = true :=
  ⟨admission.prepared.1,
    R.admitVia_vouchers_verified (R.receive_committed committed).2.2.1⟩

end PureVerdicts

end Receiver

/-! ## Premise inhabitants

A two-line journal and receiver on which `receive` reaches both `committed`
and `unauthenticated`, so the premises of `receive_committed`,
`receive_committed_verified`, `receive_committed_prepared_verified` and
`admitVia_unauthenticated` are inhabited.  Its `prepare` refuses unless the
vouchers it is handed hold its one claim: the committed outcome is reached only
through a voucher the verifier issued.  The deployed inhabitant is
`Kernel.Receivers.SubjectKeyRotation.family`. -/
namespace Fixture

def journal : Journal where
  State := List (Recorded Nat Nat Nat)
  Snap := List (Recorded Nat Nat Nat)
  snap := id
  TxId := Nat
  Event := Nat
  Nullifier := Nat
  Payload := Unit
  Intent := Recorded Nat Nat Nat
  txIdDecEq := inferInstance
  eventDecEq := inferInstance
  nullifierDecEq := inferInstance
  lookup := fun snap txId => snap.find? fun recorded => recorded.txId == txId
  intentOf := fun txId event nullifiers _ => ⟨txId, event, nullifiers⟩
  spent := fun _ => []
  install := fun snap intent => intent :: snap
  lookup_install := by intro snap txId event nullifiers payload; simp

def key : SigQuery := ⟨.ed25519, [1], [2], [3]⟩

def receiver (v : SigQuery → Bool) : Receiver journal (Receiver.pureVerifier v) where
  Env := Unit
  Ingress := Nat
  Command := Nat
  Reject := Unit
  Prepared := fun _ _ _ => Unit
  decode := fun bytes => bytes.head?.map UInt8.toNat
  command := id
  claims := fun _ _ _ => .ok [key]
  observations := fun _ _ _ => .ok []
  prepare := fun vouchers _ _ _ =>
    match vouchers.signed? .ed25519 key.publicKey key.message with
    | some _ => .ok ()
    | none => .error ()
  shape := fun _ => true
  Fault := Empty
  lawFault := fun _ => none
  txId := fun _ ingress => ingress
  event := fun _ ingress => ingress + 1
  nullifiers := fun _ ingress => [ingress]
  payload := fun _ _ => ()

/-- The fixture store's exact-append witness is a bare token. -/
abbrev Exact : journal.State → journal.Intent → Type := fun _ _ => Unit

def append : (state : journal.State) → (intent : journal.Intent) →
    Id (Receiver.Commit (Exact state intent) Unit) :=
  fun _ _ => pure (.exact ())

theorem committed_reachable :
    ∃ ingress admission witness,
      (receiver fun _ => true).receive (Exact := Exact) (Other := Unit) append () [] [7] =
        pure (.committed ingress admission witness) :=
  ⟨_, _, _, rfl⟩

theorem unauthenticated_reachable :
    (receiver fun _ => false).receive (Exact := Exact) (Other := Unit) append () [] [7] =
      pure (.refused (.unauthenticated key)) :=
  rfl

/-- The fixture's `prepare` refuses under the empty vouchers: the gate's
"signed" branch is reachable only through `admitVia`. -/
theorem prepare_unvouched_refused (v : SigQuery → Bool) :
    (receiver v).prepare Vouchers.empty () [] (7 : Nat) = .error () :=
  rfl

end Fixture

#assert_axioms firstRefused_none_iff
#assert_axioms firstRefused_some
#assert_axioms Vouchers.vouches_iff
#assert_axioms Vouchers.signed?_some
#assert_axioms Receiver.admit_signature_first
#assert_axioms Receiver.admit_ok_iff
#assert_axioms Receiver.admit_law_refused
#assert_axioms Receiver.admit_ok_of
#assert_axioms Receiver.Admitted.lawful
#assert_axioms Receiver.Admitted.prepared
#assert_axioms Receiver.receive_committed_lawFault
#assert_axioms Receiver.guardsOff_readonly
#assert_axioms Receiver.guardsOff_complete
#assert_axioms Receiver.replay_only_original
#assert_axioms Receiver.replay_after_install
#assert_axioms Receiver.verifyAll_pure
#assert_axioms Receiver.observeAll_pure
#assert_axioms Receiver.observeAll_sound
#assert_axioms Receiver.admitVia_observed
#assert_axioms Receiver.takeWhile_vouched
#assert_axioms Receiver.admitVia_vouchers_verified
#assert_axioms Receiver.admitVia_claims_verified
#assert_axioms Receiver.admitVia_unauthenticated
#assert_axioms Receiver.receive_committed
#assert_axioms Receiver.verifyAll_sound
#assert_axioms Receiver.admitVia_refused_before_prepare
#assert_axioms Receiver.receive_committed_verified
#assert_axioms Receiver.receive_committed_prepared_verified
#assert_axioms Fixture.committed_reachable
#assert_axioms Fixture.unauthenticated_reachable
#assert_axioms Fixture.prepare_unvouched_refused

end Minidregg.Theory.Receiving
