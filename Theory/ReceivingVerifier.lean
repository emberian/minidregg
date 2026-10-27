/-
# Theory.ReceivingVerifier -- the signature oracle's answer, carried by the voucher

A receiver's `prepare` is handed `Vouchers`: the claims its verifier accepted and the
answers it observed.  Until now a `Vouchers` was two bare lists under a `private mk`
(`TokenCensus` defect row `Theory.Receiving.Vouchers.mk`): `by constructor` forged a
voucher for a signature nobody checked, and the verifier `SigQuery -> m (Except String Bool)`
lives in an arbitrary monad, so no proposition about its answer could be stated.

Here the verifier is a structure.  It names the relation `Answered q b` ("the oracle answered `b`
on exactly the query `q`") and its `ask` returns the answer WITH that proof, so an answer cannot
be produced without the oracle having given it.  `Vouchers` is indexed by the verifier and
carries `verifiedAnswered` / `observedAnswered`: every voucher is a query the verifier answered
`true`, every observation the answer it gave.

* At `Id` (`pureVerifier v`) `Answered q b := v q = b`: nothing is trusted.
* At `IO` the relation is `Compiler.CredentialSignatureAdmission.Ran`, introduced only by the
  shim around `CredentialSignatureIO.verify` (one constructor site, a `restricted` census row).
  That shim is the one remaining layer-2 trust, and it is named.

Poles (ATLAS statement fields): satisfiable `Vouchers.exists_for_true`; teeth
`Vouchers.not_verified_of_not_answered`, `Vouchers.pure_false_not_verified`,
`Vouchers.pure_observed_eq`; premise inhabitation `pureVerifier_poles`, `Verifier.exists_refuting`.
-/
import Theory.AssertAxioms

namespace Minidregg.Theory.Receiving

set_option autoImplicit false

/-! ## Signature claims -/

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

/-! ## The verifier -/

/-- **A signature verifier in the monad `m`, with the relation it answers by.**
`Answered q b` says the oracle answered `b` on exactly the query `q`; `ask` returns the
answer together with that fact, so no answer exists that the oracle did not give. -/
structure Verifier (m : Type → Type) where
  Answered : SigQuery → Bool → Prop
  ask : (query : SigQuery) → m (Except String {answer : Bool // Answered query answer})

/-- The verifier that answers `v`, at `Id`: `Answered q b` is `v q = b`, so the fact is `rfl`. -/
def pureVerifier (v : SigQuery → Bool) : Verifier Id where
  Answered := fun query answer => v query = answer
  ask := fun query => pure (.ok ⟨v query, rfl⟩)

/-! ## The voucher -/

/-- **The claims a receiver's verifier accepted**, as `prepare` receives them, WITH the oracle's
answer: `verifiedAnswered` (each voucher is a query the verifier answered `true`) and
`observedAnswered` (each observation carries the answer the verifier gave).  Indexed by the
verifier: a value minted under one verifier is not a value of another's type.  The constructor is
private to this module; `Vouchers.empty` and `Vouchers.ofAnswered` are the only constructor calls, and
`ofAnswered` is public BY DESIGN: it demands the two propositions, so it mints nothing the verifier
did not answer.  `Receiver.admitVia` is the one caller that obtains those propositions, from
`Verifier.ask`.  **Layer 1**: the guarantee is the propositions, stated about the verifier's `Answered`.
`Verifier` is an open structure, so the guarantee is only as strong as the `Answered` of the verifier
a receiver is indexed by: Theory cannot name the live one, so `Kernel.Receiving.Family.receiver` fixes it
to `receiverVerifier` (Answered = `Ran`, one private-constructor site) and
`scripts/check-receiver-verifier.sh` refuses any other. -/
structure Vouchers {m : Type → Type} (V : Verifier m) where
  private mk ::
  verified : List SigQuery
  /-- The receiver's OBSERVED signatures, each with the verifier's answer: a `false` is
  information the family decides on (it does not refuse), an error refused the ingress before
  anything was minted. -/
  observed : List (SigQuery × Bool)
  verifiedAnswered : ∀ query ∈ verified, V.Answered query true
  observedAnswered : ∀ answered ∈ observed, V.Answered answered.1 answered.2

namespace Vouchers

variable {m : Type → Type} {V : Verifier m}

/-- The vouchers of nothing: vacuously answered. -/
def empty : Vouchers V := ⟨[], [], by simp, by simp⟩

/-- Mint from answered lists.  The only constructor call outside `empty`, so the proofs are
required at every mint. -/
def ofAnswered (verified : List SigQuery) (observed : List (SigQuery × Bool))
    (verifiedAnswered : ∀ query ∈ verified, V.Answered query true)
    (observedAnswered : ∀ answered ∈ observed, V.Answered answered.1 answered.2) : Vouchers V :=
  ⟨verified, observed, verifiedAnswered, observedAnswered⟩

/-- The oracle a voucher set answers: exactly its claims. -/
def vouches (vouchers : Vouchers V) (claim : SigQuery) : Bool := decide (claim ∈ vouchers.verified)

theorem vouches_iff (vouchers : Vouchers V) (claim : SigQuery) :
    vouchers.vouches claim = true ↔ claim ∈ vouchers.verified := by
  simp [vouches]

/-- The vouched claim under this scheme with this key and message, if any. -/
def signed? (vouchers : Vouchers V) (scheme : Scheme) (publicKey message : List UInt8) :
    Option SigQuery :=
  vouchers.verified.find? fun claim =>
    claim.scheme == scheme && claim.publicKey == publicKey && claim.message == message

theorem signed?_some {vouchers : Vouchers V} {scheme : Scheme} {publicKey message : List UInt8}
    {claim : SigQuery} (found : vouchers.signed? scheme publicKey message = some claim) :
    claim ∈ vouchers.verified ∧ claim.scheme = scheme ∧ claim.publicKey = publicKey ∧
      claim.message = message := by
  refine ⟨List.mem_of_find?_eq_some found, ?_⟩
  simpa [and_assoc] using List.find?_some found

theorem empty_verified : (empty : Vouchers V).verified = [] := rfl

/-- The verifier's answer on an observed query, if the receiver observed it. -/
def answer? (vouchers : Vouchers V) (query : SigQuery) : Option Bool :=
  (vouchers.observed.find? fun answered => answered.1 == query).map Prod.snd

theorem answer?_some {vouchers : Vouchers V} {query : SigQuery} {answer : Bool}
    (found : vouchers.answer? query = some answer) : (query, answer) ∈ vouchers.observed := by
  unfold answer? at found
  obtain ⟨answered, hit, rfl⟩ := Option.map_eq_some_iff.1 found
  have same : answered.1 = query := by simpa using List.find?_some hit
  have member := List.mem_of_find?_eq_some hit
  obtain ⟨q, b⟩ := answered
  cases same
  exact member

/-- **The census witness**: a voucher set states, about its own verifier `V`, that every voucher was
answered `true` and every observation was answered as recorded. -/
theorem Vouchers.answered {m : Type → Type} {V : Verifier m} (vouchers : Vouchers V) :
    (∀ query ∈ vouchers.verified, V.Answered query true) ∧
      ∀ answered ∈ vouchers.observed, V.Answered answered.1 answered.2 :=
  ⟨vouchers.verifiedAnswered, vouchers.observedAnswered⟩

/-! ### The statement's poles -/

/-- **Teeth (general).** A voucher for a query the verifier did not answer `true` cannot exist. -/
theorem not_verified_of_not_answered (vouchers : Vouchers V) {query : SigQuery}
    (unanswered : ¬ V.Answered query true) : query ∉ vouchers.verified :=
  fun member => unanswered (vouchers.verifiedAnswered query member)

/-- **Teeth (pure oracle).** Under `pureVerifier v`, no voucher set holds a query whose oracle
answer is `false`: the statement a forger would need to falsify. -/
theorem pure_false_not_verified {v : SigQuery → Bool} (vouchers : Vouchers (pureVerifier v))
    {query : SigQuery} (refused : v query = false) : query ∉ vouchers.verified := by
  refine not_verified_of_not_answered vouchers ?_
  intro answered
  have : v query = true := answered
  rw [refused] at this
  cases this

/-- An observation under `pureVerifier v` is exactly the oracle's answer. -/
theorem pure_observed_eq {v : SigQuery → Bool} (vouchers : Vouchers (pureVerifier v))
    {answered : SigQuery × Bool} (member : answered ∈ vouchers.observed) :
    v answered.1 = answered.2 :=
  vouchers.observedAnswered answered member

/-- **Satisfiable.** For a query the pure oracle accepts, a voucher set holding it exists
(`Fixture.vouchers_minted_by_admitVia` restates this through `Receiver.admitVia`). -/
theorem exists_for_true {v : SigQuery → Bool} {query : SigQuery} (accepted : v query = true) :
    ∃ vouchers : Vouchers (pureVerifier v), query ∈ vouchers.verified :=
  ⟨ofAnswered [query] [(query, true)]
    (by intro q member; simp at member; subst member; exact accepted)
    (by intro a member; simp at member; subst member; exact accepted),
    by simp [ofAnswered]⟩

end Vouchers

/-! ### Premise inhabitation -/

/-- A concrete query and the pure oracle `message = [1]`: it answers `true` on one query and
`false` on another, so both poles of `Answered` are inhabited. -/
theorem pureVerifier_poles :
    let accepted : SigQuery := ⟨.ed25519, [1], [1], [3]⟩
    let refused : SigQuery := ⟨.ed25519, [1], [2], [3]⟩
    let v : SigQuery → Bool := fun query => query.message == [1]
    (pureVerifier v).Answered accepted true ∧ (pureVerifier v).Answered refused false :=
  ⟨rfl, rfl⟩

/-- A verifier exists for which a query is not answered `true` (so the teeth theorem has a
non-vacuous premise). -/
theorem Verifier.exists_refuting :
    ∃ (V : Verifier Id) (query : SigQuery), ¬ V.Answered query true :=
  ⟨pureVerifier fun _ => false, ⟨.ed25519, [], [], []⟩, by
    intro answered
    have : false = true := answered
    cases this⟩

#assert_axioms Vouchers.answered
#assert_axioms Vouchers.vouches_iff
#assert_axioms Vouchers.signed?_some
#assert_axioms Vouchers.answer?_some
#assert_axioms Vouchers.not_verified_of_not_answered
#assert_axioms Vouchers.pure_false_not_verified
#assert_axioms Vouchers.pure_observed_eq
#assert_axioms Vouchers.exists_for_true
#assert_axioms pureVerifier_poles
#assert_axioms Verifier.exists_refuting

end Minidregg.Theory.Receiving
