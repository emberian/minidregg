/-
# Theory.Receiving -- one receiving pipeline, its laws proved once

Every native receiver on Mini does the same five things: decode signed bytes,
recognise an exact retry in the journal, authenticate the signatures the command
names, prepare the gate-checked per-cell patch, and append one durable intent by
compare-and-swap.  Until this module each receiving family retyped that skeleton
(`Reject`, `Accepted`, `Result`, `Prepared`, `receiveLoaded`, `replay`,
`readGuards_readonly`, `requireSome`), and most of them prepared -- re-executed
-- before they verified a signature (`docs/design/RECEIVER.md`, the census).

Here the skeleton is one definition over an abstract journal (`Journal`) and an
arbitrary monad.  `Kernel.Receiving` instantiates the journal with the deployed
durable layer and runs `receive` in `IO`; the theorems below are about that same
definition, read at `Id` where a statement needs the verifier's verdicts.

* `admit_signature_first` -- an ingress one of whose signature claims the
  verdict oracle refuses is refused `unauthenticated`, with a refusal computed
  from the claims and the verdicts alone: neither `prepare` (the gate, the
  re-execution) nor the shape check is consulted.  Every receiver, any `prepare`.
* `admit_ok_iff` -- admission is exactly: the claims resolve, every claim is
  vouched for, preparation succeeds, the shape check passes, and the written
  cells' laws raise no fault.
* `admitVia_vouches_only_verified`, `admitVia_claims_verified` -- the oracle
  `admitVia` builds vouches only for claims the verifier accepted, so an
  admitted ingress had every claim verified; `admitVia_unauthenticated` -- a
  claim the verifier refuses refuses the ingress before preparation.
* `guardsOff_readonly`, `guardsOff_complete` -- read guards are never on a
  written cell, and no guard on an unwritten cell is dropped.
* `replay_only_original`, `replay_after_install` -- a retry is confirmed only by
  the journal record of the same transaction with the same event and
  nullifiers, and the record live admission installs is exactly one replay
  confirms (replay = live admission).
* `receive_committed_admitted` -- a committed outcome of `receive` is an
  admission by `admitVia` over the same verifier, followed by the append.
-/
import Theory.AssertAxioms

namespace Minidregg.Theory.Receiving

set_option autoImplicit false

/-! ## Signature claims and the verdict oracle -/

/-- One signature obligation: the exact key, the exact signed message, and the
presented signature.  A receiver names these from the decoded ingress and, for
keys held in state, a key lookup; never from preparation. -/
structure SigQuery where
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
  install : Snap → Intent → Snap
  lookup_install : ∀ snap txId event nullifiers payload,
    lookup (install snap (intentOf txId event nullifiers payload)) txId = some ⟨txId, event, nullifiers⟩

instance (J : Journal) : DecidableEq J.TxId := J.txIdDecEq
instance (J : Journal) : DecidableEq J.Event := J.eventDecEq
instance (J : Journal) : DecidableEq J.Nullifier := J.nullifierDecEq

/-! ## The receiver declaration -/

/-- One receiving family: its codec, its command, the signature claims it
makes, its gate and per-cell patch (`prepare`, `payload`), its shape check, and
its journal identity (`txId`, `event`, `nullifiers`).  Everything else -- the
order of the steps, the refusal type, the accepted object, replay, the outcome
-- is defined once below. -/
structure Receiver (J : Journal) where
  Env : Type
  Ingress : Type
  Command : Type
  Reject : Type
  Prepared : Env → J.State → Command → Type
  decode : List UInt8 → Option Ingress
  command : Ingress → Command
  /-- The signature claims: from the decoded ingress and a key lookup. -/
  claims : Env → J.State → Ingress → Except Reject (List SigQuery)
  /-- The gate and the patch: the only step that may re-execute anything. -/
  prepare : (env : Env) → (state : J.State) → (command : Command) →
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

variable (R : Receiver J)

/-- An admitted ingress: only `admit` constructs one. -/
structure Accepted (env : R.Env) (state : J.State) (ingress : R.Ingress) where
  private mk ::
  prepared : R.Prepared env state (R.command ingress)

/-- Admission over a verdict oracle: authenticate every claim, then prepare,
then check the physical shape, then the written cells' laws.  The order is the
content of `admit_signature_first`. -/
def admit (env : R.Env) (state : J.State) (ingress : R.Ingress) (ok : SigQuery → Bool) :
    Except (Refusal R.Reject R.Fault) (R.Accepted env state ingress) :=
  match R.claims env state ingress with
  | .error reason => .error (.family reason)
  | .ok claims =>
      match firstRefused ok claims with
      | some claim => .error (.unauthenticated claim)
      | none =>
          match R.prepare env state (R.command ingress) with
          | .error reason => .error (.family reason)
          | .ok prepared =>
              if R.shape prepared then
                match R.lawFault prepared with
                | none => .ok ⟨prepared⟩
                | some fault => .error (.law fault)
              else .error .shape

/-- **Signature before any re-execution.**  When a claim is refused, admission
is the `unauthenticated` refusal of the first refused claim -- a value fixed by
the claims and the oracle alone.  The statement holds for every receiver, so
for every `prepare` and `shape`: neither is consulted. -/
theorem admit_signature_first {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {ok : SigQuery → Bool} {claims : List SigQuery} {claim : SigQuery}
    (resolved : R.claims env state ingress = .ok claims)
    (refused : firstRefused ok claims = some claim) :
    R.admit env state ingress ok = .error (.unauthenticated claim) := by
  simp [admit, resolved, refused]

/-- **Admission, exactly.** -/
theorem admit_ok_iff {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {ok : SigQuery → Bool} (accepted : R.Accepted env state ingress) :
    R.admit env state ingress ok = .ok accepted ↔
      ∃ claims, R.claims env state ingress = .ok claims ∧
        (∀ claim ∈ claims, ok claim = true) ∧
        R.prepare env state (R.command ingress) = .ok accepted.prepared ∧
        R.shape accepted.prepared = true ∧ R.lawFault accepted.prepared = none := by
  obtain ⟨prepared⟩ := accepted
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
              exact ⟨claims, resolved, (firstRefused_none_iff ok claims).1 none_refused,
                preparedEq, shaped, lawful⟩
            · cases admitted
          · cases admitted
  · rintro ⟨claims, resolved, verified, preparedEq, shaped, lawful⟩
    simp only [resolved, (firstRefused_none_iff ok claims).2 verified, preparedEq, shaped,
      lawful, if_true]

/-- **A law fault refuses**, naming the fault: a patch that prepares and passes
the physical shape but whose laws raise `fault` is refused `law fault`. -/
theorem admit_law_refused {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {ok : SigQuery → Bool} {claims : List SigQuery}
    {prepared : R.Prepared env state (R.command ingress)} {fault : R.Fault}
    (resolved : R.claims env state ingress = .ok claims)
    (verified : ∀ claim ∈ claims, ok claim = true)
    (preparedEq : R.prepare env state (R.command ingress) = .ok prepared)
    (shaped : R.shape prepared = true) (faulted : R.lawFault prepared = some fault) :
    R.admit env state ingress ok = .error (.law fault) := by
  simp [admit, resolved, (firstRefused_none_iff ok claims).2 verified, preparedEq, shaped, faulted]

/-! ## The verifier, and admission through it -/

/-- Verify the claims in order, stopping at the first refusal; the result is
the claims the verifier accepted (a prefix of `claims`). -/
def verifyAll {m : Type → Type} [Monad m] (verify : SigQuery → m (Except String Bool)) :
    List SigQuery → m (Except String (List SigQuery))
  | [] => pure (.ok [])
  | claim :: rest => do
      match ← verify claim with
      | .error detail => pure (.error detail)
      | .ok false => pure (.ok [])
      | .ok true =>
          match ← verifyAll verify rest with
          | .error detail => pure (.error detail)
          | .ok verified => pure (.ok (claim :: verified))

/-- The oracle of a verified list: it vouches for exactly those claims. -/
def vouches (verified : List SigQuery) (claim : SigQuery) : Bool := decide (claim ∈ verified)

/-- An admission together with the oracle it was made under. -/
structure Admitted (env : R.Env) (state : J.State) (ingress : R.Ingress) where
  ok : SigQuery → Bool
  accepted : R.Accepted env state ingress
  admitted : R.admit env state ingress ok = .ok accepted

/-- **Every admission is lawful**: its prepared patch passed the physical shape
and its laws raised no fault. -/
theorem Admitted.lawful {R : Receiver J} {env : R.Env} {state : J.State} {ingress : R.Ingress}
    (admission : R.Admitted env state ingress) :
    R.shape admission.accepted.prepared = true ∧ R.lawFault admission.accepted.prepared = none := by
  obtain ⟨-, -, -, -, shaped, lawful⟩ := (R.admit_ok_iff admission.accepted).1 admission.admitted
  exact ⟨shaped, lawful⟩

/-- The one admission path: resolve claims, verify them, admit.  The live
receiver and the audit walk both call this, so the walk's re-admission is the
live admission. -/
def admitVia {m : Type → Type} [Monad m] (verify : SigQuery → m (Except String Bool))
    (env : R.Env) (state : J.State) (ingress : R.Ingress) :
    m (Except (Refusal R.Reject R.Fault) (R.Admitted env state ingress)) := do
  match R.claims env state ingress with
  | .error reason => pure (.error (.family reason))
  | .ok claims =>
      match ← verifyAll verify claims with
      | .error detail => pure (.error (.verifier detail))
      | .ok verified =>
          match admitted : R.admit env state ingress (vouches verified) with
          | .error reason => pure (.error reason)
          | .ok accepted => pure (.ok ⟨vouches verified, accepted, admitted⟩)

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
the journal holds this transaction with this event and these nullifiers; a
conflict otherwise. -/
def replay (env : R.Env) (state : J.State) (ingress : R.Ingress) :
    Option (Except Unit (J.TxId × J.Event)) :=
  match J.lookup (J.snap state) (R.txId env ingress) with
  | none => none
  | some recorded =>
      if recorded = ⟨R.txId env ingress, R.event env ingress, R.nullifiers env ingress⟩ then
        some (.ok (R.receipt env ingress))
      else some (.error ())

/-- **Replay confirms only the original.** -/
theorem replay_only_original {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {selected : J.TxId × J.Event} (found : R.replay env state ingress = some (.ok selected)) :
    selected = R.receipt env ingress ∧
      J.lookup (J.snap state) (R.txId env ingress) =
        some ⟨R.txId env ingress, R.event env ingress, R.nullifiers env ingress⟩ := by
  unfold replay at found
  split at found
  · cases found
  · rename_i recorded looked
    split at found
    · rename_i exact
      cases found
      exact ⟨rfl, looked.trans (congrArg some exact)⟩
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
  simp

/-- One append attempt: the store's evidence that exactly this intent was
appended, or any other settlement. -/
inductive Commit (Exact : Type) (Other : Type) where
  | exact (witness : Exact)
  | other (outcome : Other)

/-- What one receipt attempt produced. -/
inductive Outcome (env : R.Env) (state : J.State)
    (Exact : J.State → J.Intent → Type) (Other : Type) where
  | replayed (receipt : J.TxId × J.Event)
  | conflict
  | refused (reason : Refusal R.Reject R.Fault)
  | committed (ingress : R.Ingress) (admission : R.Admitted env state ingress)
      (witness : Exact state (R.intent admission.accepted))
  | durable (ingress : R.Ingress) (outcome : Other)

/-- **The receiving pipeline**, the one copy: decode, exact retry, admission
(`admitVia`: claims, verification, then preparation), append. -/
def receive {m : Type → Type} [Monad m] {Exact : J.State → J.Intent → Type} {Other : Type}
    (verify : SigQuery → m (Except String Bool))
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
          match ← R.admitVia verify env state ingress with
          | .error reason => pure (.refused reason)
          | .ok admission =>
              match ← append state (R.intent admission.accepted) with
              | .exact witness => pure (.committed ingress admission witness)
              | .other outcome => pure (.durable ingress outcome)

/-! ## The verifier's verdicts, read at `Id` -/

section Verdicts

variable (v : SigQuery → Bool)

/-- The verifier that answers `v`. -/
def pureVerifier : SigQuery → Id (Except String Bool) := fun claim => pure (.ok (v claim))

/-- At `Id`, the verifier accepts exactly the longest prefix it vouches for. -/
theorem verifyAll_pure :
    ∀ claims : List SigQuery,
      verifyAll (pureVerifier v) claims = (pure (.ok (claims.takeWhile v)) : Id _)
  | [] => rfl
  | claim :: rest => by
      cases accepted : v claim
      · simp [verifyAll, pureVerifier, accepted]
      · have tail := verifyAll_pure rest
        simp only [verifyAll, pureVerifier, bind, pure] at tail ⊢
        simp [accepted, tail]

theorem takeWhile_vouched :
    ∀ {claims : List SigQuery} {claim : SigQuery}, claim ∈ claims.takeWhile v → v claim = true
  | [], _, member => by simp at member
  | head :: rest, claim, member => by
      cases verdict : v head
      · simp [verdict] at member
      · simp only [List.takeWhile_cons, verdict] at member
        rcases List.mem_cons.mp member with same | later
        · exact same ▸ verdict
        · exact takeWhile_vouched later

theorem vouches_takeWhile {claims : List SigQuery} {claim : SigQuery}
    (vouched : vouches (claims.takeWhile v) claim = true) : v claim = true := by
  simp only [vouches, decide_eq_true_eq] at vouched
  exact takeWhile_vouched v vouched

/-- **The oracle vouches only for verified claims.** -/
theorem admitVia_vouches_only_verified {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {admission : R.Admitted env state ingress}
    (admitted : R.admitVia (pureVerifier v) env state ingress = (pure (.ok admission) : Id _)) :
    ∀ claim, admission.ok claim = true → v claim = true := by
  unfold admitVia at admitted
  split at admitted
  · cases admitted
  · rename_i claims _
    rw [show (verifyAll (pureVerifier v) claims >>= _) = _ from
      congrArg (· >>= _) (verifyAll_pure v claims)] at admitted
    simp only [bind, pure] at admitted
    split at admitted
    · cases admitted
    · cases admitted
      intro claim vouched
      exact vouches_takeWhile v vouched

/-- **An admitted ingress had every claim verified.** -/
theorem admitVia_claims_verified {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {admission : R.Admitted env state ingress}
    (admitted : R.admitVia (pureVerifier v) env state ingress = (pure (.ok admission) : Id _)) :
    ∃ claims, R.claims env state ingress = .ok claims ∧ ∀ claim ∈ claims, v claim = true := by
  obtain ⟨claims, resolved, vouched, -, -, -⟩ := (R.admit_ok_iff admission.accepted).1 admission.admitted
  exact ⟨claims, resolved, fun claim member =>
    R.admitVia_vouches_only_verified v admitted claim (vouched claim member)⟩

/-- **A refused signature refuses before preparation**, through the live path:
if the verifier refuses one of the claims, `admitVia` returns an
`unauthenticated` refusal naming one of the claims -- never an admission, and
never a `family` refusal that `prepare` could have produced. -/
theorem admitVia_unauthenticated {env : R.Env} {state : J.State} {ingress : R.Ingress}
    {claims : List SigQuery} {bad : SigQuery}
    (resolved : R.claims env state ingress = .ok claims)
    (member : bad ∈ claims) (refused : v bad = false) :
    ∃ claim, claim ∈ claims ∧
      R.admitVia (pureVerifier v) env state ingress =
        (pure (.error (.unauthenticated claim)) : Id _) := by
  have notNone : firstRefused (vouches (claims.takeWhile v)) claims ≠ none := by
    intro none_refused
    have := (firstRefused_none_iff _ claims).1 none_refused bad member
    rw [vouches_takeWhile v this] at refused
    cases refused
  obtain ⟨claim, found⟩ := Option.ne_none_iff_exists'.1 notNone
  obtain ⟨claimMember, -⟩ := firstRefused_some found
  refine ⟨claim, claimMember, ?_⟩
  unfold admitVia
  simp only [resolved]
  rw [show (verifyAll (pureVerifier v) claims >>= _) = _ from
    congrArg (· >>= _) (verifyAll_pure v claims)]
  simp only [bind, pure]
  split
  · rename_i reason refusedEq
    rw [R.admit_signature_first resolved found] at refusedEq
    cases refusedEq
    rfl
  · rename_i accepted admittedEq
    rw [R.admit_signature_first resolved found] at admittedEq
    cases admittedEq

/-- **A committed outcome is a fresh, admitted, appended ingress**: the bytes
decoded, the journal did not hold the transaction, `admitVia` (claims, the
verifier, then preparation) admitted it, and the append returned exactly the
witness the outcome carries. -/
theorem receive_committed {verify : SigQuery → Id (Except String Bool)}
    {Exact : J.State → J.Intent → Type} {Other : Type}
    {append : (state : J.State) → (intent : J.Intent) → Id (Commit (Exact state intent) Other)}
    {env : R.Env} {state : J.State} {bytes : List UInt8} {ingress : R.Ingress}
    {admission : R.Admitted env state ingress} {witness : Exact state (R.intent admission.accepted)}
    (committed : R.receive verify append env state bytes = pure (.committed ingress admission witness)) :
    R.decode bytes = some ingress ∧ R.replay env state ingress = none ∧
      R.admitVia verify env state ingress = pure (.ok admission) ∧
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

/-- At the pure verifier: a committed ingress had every claim verified. -/
theorem receive_committed_verified (v : SigQuery → Bool)
    {Exact : J.State → J.Intent → Type} {Other : Type}
    {append : (state : J.State) → (intent : J.Intent) → Id (Commit (Exact state intent) Other)}
    {env : R.Env} {state : J.State} {bytes : List UInt8} {ingress : R.Ingress}
    {admission : R.Admitted env state ingress} {witness : Exact state (R.intent admission.accepted)}
    (committed : R.receive (pureVerifier v) append env state bytes =
      pure (.committed ingress admission witness)) :
    ∃ claims, R.claims env state ingress = .ok claims ∧ ∀ claim ∈ claims, v claim = true :=
  R.admitVia_claims_verified v (R.receive_committed committed).2.2.1

/-- **A committed ingress is lawful**: the admission a committed outcome carries
passed the physical shape and raised no law fault. -/
theorem receive_committed_lawFault {verify : SigQuery → Id (Except String Bool)}
    {Exact : J.State → J.Intent → Type} {Other : Type}
    {append : (state : J.State) → (intent : J.Intent) → Id (Commit (Exact state intent) Other)}
    {env : R.Env} {state : J.State} {bytes : List UInt8} {ingress : R.Ingress}
    {admission : R.Admitted env state ingress} {witness : Exact state (R.intent admission.accepted)}
    (_committed : R.receive verify append env state bytes = pure (.committed ingress admission witness)) :
    R.shape admission.accepted.prepared = true ∧ R.lawFault admission.accepted.prepared = none :=
  admission.lawful

end Verdicts

end Receiver

/-! ## Premise inhabitants

A two-line journal and receiver on which `receive` reaches both `committed`
and `unauthenticated`, so the premises of `receive_committed`,
`receive_committed_verified` and `admitVia_unauthenticated` are inhabited.  The
deployed inhabitant is `Kernel.Receivers.SubjectKeyRotation.receiver`. -/
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
  install := fun snap intent => intent :: snap
  lookup_install := by intro snap txId event nullifiers payload; simp

def key : SigQuery := ⟨[1], [2], [3]⟩

def receiver : Receiver journal where
  Env := Unit
  Ingress := Nat
  Command := Nat
  Reject := Unit
  Prepared := fun _ _ _ => Unit
  decode := fun bytes => bytes.head?.map UInt8.toNat
  command := id
  claims := fun _ _ _ => .ok [key]
  prepare := fun _ _ _ => .ok ()
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
      receiver.receive (Exact := Exact) (Other := Unit)
          (Receiver.pureVerifier fun _ => true) append () [] [7] =
        pure (.committed ingress admission witness) :=
  ⟨_, _, _, rfl⟩

theorem unauthenticated_reachable :
    receiver.receive (Exact := Exact) (Other := Unit)
        (Receiver.pureVerifier fun _ => false) append () [] [7] =
      pure (.refused (.unauthenticated key)) :=
  rfl

end Fixture

#assert_axioms firstRefused_none_iff
#assert_axioms firstRefused_some
#assert_axioms Receiver.admit_signature_first
#assert_axioms Receiver.admit_ok_iff
#assert_axioms Receiver.admit_law_refused
#assert_axioms Receiver.Admitted.lawful
#assert_axioms Receiver.receive_committed_lawFault
#assert_axioms Receiver.guardsOff_readonly
#assert_axioms Receiver.guardsOff_complete
#assert_axioms Receiver.replay_only_original
#assert_axioms Receiver.replay_after_install
#assert_axioms Receiver.verifyAll_pure
#assert_axioms Receiver.takeWhile_vouched
#assert_axioms Receiver.vouches_takeWhile
#assert_axioms Receiver.admitVia_vouches_only_verified
#assert_axioms Receiver.admitVia_claims_verified
#assert_axioms Receiver.admitVia_unauthenticated
#assert_axioms Receiver.receive_committed
#assert_axioms Receiver.receive_committed_verified
#assert_axioms Fixture.committed_reachable
#assert_axioms Fixture.unauthenticated_reachable

end Minidregg.Theory.Receiving
