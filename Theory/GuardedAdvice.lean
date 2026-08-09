/-
# Theory.GuardedAdvice -- eager guarded holes, untrusted advice, and durable consumption

This file is the candidate-independent guarded-advice nucleus.  A `HoleSpec`
fixes every part of the transition shape before any advice arrives.  `Advice`
is dependent on that exact specification and contributes only a value of the
logical type selected by the specification's first-order code.

Verification and commitment are deliberately separate:

* `verifyFill` is total and is the only constructor path to `VerifiedFill`;
* `commitFill` is a tiny durable compare-and-swap/nullifier model;
* every refusal is explicit, and only `CommitOutcome.committed` carries a new
  store.

No receipt format, runtime transport, or candidate proof system is chosen here.
-/
import Theory.IndexedProgram

namespace Minidregg.Theory.GuardedAdvice

open IndexedProgram

universe u v w

/-! ## Eager vocabulary and late advice -/

/-- Abstract carriers needed to state a guarded fill without choosing a
candidate ledger, hash, authority algebra, clock, or continuation encoding. -/
structure Vocabulary where
  HoleId : Type u
  TurnId : Type u
  Root : Type u
  AuthorityDemand : Type u
  Footprint : Type u
  Commitment : Type u
  Height : Type u
  Continuation : Type u
  NullifierDomain : Type u

/-- The complete eager shape of a guarded hole.  In particular, the late
party cannot choose a code/codec, turn, root, authority demand, footprint,
guard, effect, deadline, continuation, or replay domain. -/
structure HoleSpec (U : FirstOrderUniverse.{u, v}) (V : Vocabulary.{w}) where
  holeId : V.HoleId
  code : U.Code
  turnId : V.TurnId
  preRoot : V.Root
  authorityDemand : V.AuthorityDemand
  footprint : V.Footprint
  guardCommitment : V.Commitment
  effectCommitment : V.Commitment
  deadline : V.Height
  continuation : V.Continuation
  nullifierDomain : V.NullifierDomain

/-- The codec is selected eagerly by `HoleSpec.code`; it is not advice. -/
def HoleSpec.codec {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    (spec : HoleSpec U V) : LawfulCodec (U.El spec.code) :=
  U.codec spec.code

/-- Late, untrusted advice contains exactly one thing: a value of the logical
type selected by the exact hole specification.  There is no shape field to
substitute. -/
structure Advice {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    (spec : HoleSpec U V) where
  value : U.El spec.code

/-- The dependent advice value crosses its fixed codec losslessly. -/
@[simp] theorem Advice.codec_roundtrip
    {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    {spec : HoleSpec U V} (advice : Advice spec) :
    spec.codec.decode (spec.codec.encode advice.value) = some advice.value :=
  spec.codec.decode_encode advice.value

/-! ## Total verification -/

/-- Semantic reasons for rejecting well-typed advice.  Unsupported operations,
backend outage, pending resolution, and expiry are separate outcomes below and
therefore cannot be confused with a policy rejection. -/
inductive RejectReason
  | authority
  | guard
  | effect
deriving DecidableEq, Repr

/-- The trusted checks for this abstract vocabulary.  Search, transport, and
proof production may be adversarial; acceptance is defined only by these
checks. -/
structure FillVerifier (U : FirstOrderUniverse.{u, v}) (V : Vocabulary.{w}) where
  supports : HoleSpec U V → Bool
  backendAvailable : HoleSpec U V → Bool
  ready : (spec : HoleSpec U V) → Advice spec → Bool
  authorityAccepts : (spec : HoleSpec U V) → Advice spec → Bool
  guardAccepts : (spec : HoleSpec U V) → Advice spec → Bool
  effectAccepts : (spec : HoleSpec U V) → Advice spec → Bool
  postRoot : (spec : HoleSpec U V) → Advice spec → V.Root

/-- Verifier-minted evidence.  Its private constructor and dependent indices
bind the evidence to the exact verifier, observation height, specification,
and advice that were checked. -/
structure VerifiedFill
    {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    [LinearOrder V.Height]
    (verifier : FillVerifier U V) (now : V.Height)
    (spec : HoleSpec U V) (advice : Advice spec) where
  private mk ::
  postRoot : V.Root
  postRoot_eq : postRoot = verifier.postRoot spec advice
  supported : verifier.supports spec = true
  backend_available : verifier.backendAvailable spec = true
  within_deadline : now ≤ spec.deadline
  ready : verifier.ready spec advice = true
  authority_bound : verifier.authorityAccepts spec advice = true
  guard_bound : verifier.guardAccepts spec advice = true
  effect_bound : verifier.effectAccepts spec advice = true

/-- Exhaustive verification result.  Only `accepted` contains evidence that
may be presented to the durable commit boundary. -/
inductive VerifyOutcome
    {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    [LinearOrder V.Height]
    (verifier : FillVerifier U V) (now : V.Height)
    (spec : HoleSpec U V) (advice : Advice spec) where
  | accepted (fill : VerifiedFill verifier now spec advice)
  | rejected (reason : RejectReason)
  | pending
  | expired
  | unsupported
  | backendUnavailable

/-- Total verifier.  Operational inability and temporal states are kept
distinct from semantic rejection. -/
def verifyFill
    {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    [LinearOrder V.Height]
    (verifier : FillVerifier U V) (now : V.Height)
    (spec : HoleSpec U V) (advice : Advice spec) :
    VerifyOutcome verifier now spec advice :=
  if hs : verifier.supports spec = true then
    if hb : verifier.backendAvailable spec = true then
      if hd : now ≤ spec.deadline then
        if hr : verifier.ready spec advice = true then
          if ha : verifier.authorityAccepts spec advice = true then
            if hg : verifier.guardAccepts spec advice = true then
              if he : verifier.effectAccepts spec advice = true then
                .accepted ⟨verifier.postRoot spec advice, rfl, hs, hb, hd, hr, ha, hg, he⟩
              else
                .rejected .effect
            else
              .rejected .guard
          else
            .rejected .authority
        else
          .pending
      else
        .expired
    else
      .backendUnavailable
  else
    .unsupported

/-- Recovering the specification from verified evidence is definitionally the
same eager object that indexed the advice. -/
def VerifiedFill.boundSpec
    {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    [LinearOrder V.Height]
    {verifier : FillVerifier U V} {now : V.Height}
    {spec : HoleSpec U V} {advice : Advice spec}
    (_fill : VerifiedFill verifier now spec advice) : HoleSpec U V :=
  spec

/-- **Shape binding.** Acceptance cannot substitute any eager field: the
verified object's entire specification is the exact index of the checked
advice. -/
theorem verify_accepted_binds_eager_shape
    {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    [LinearOrder V.Height]
    {verifier : FillVerifier U V} {now : V.Height}
    {spec : HoleSpec U V} {advice : Advice spec}
    {fill : VerifiedFill verifier now spec advice}
    (_h : verifyFill verifier now spec advice = .accepted fill) :
    fill.boundSpec = spec :=
  rfl

/-- Acceptance exposes the three load-bearing checks against that same bound
specification: authority, guard, and effect all admitted the typed advice. -/
theorem verify_accepted_forces_bound_checks
    {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    [LinearOrder V.Height]
    {verifier : FillVerifier U V} {now : V.Height}
    {spec : HoleSpec U V} {advice : Advice spec}
    (fill : VerifiedFill verifier now spec advice) :
    verifier.authorityAccepts spec advice = true ∧
      verifier.guardAccepts spec advice = true ∧
      verifier.effectAccepts spec advice = true :=
  ⟨fill.authority_bound, fill.guard_bound, fill.effect_bound⟩

/-! ## Tiny durable CAS/nullifier model -/

/-- The replay key is derived entirely from eager shape. -/
structure NullifierKey (V : Vocabulary.{w}) where
  domain : V.NullifierDomain
  turnId : V.TurnId
  holeId : V.HoleId

/-- The nullifier consumed by this exact hole in this exact turn/domain. -/
def HoleSpec.nullifierKey
    {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    (spec : HoleSpec U V) : NullifierKey V :=
  ⟨spec.nullifierDomain, spec.turnId, spec.holeId⟩

/-- Minimal durable state: a CAS root and a persistent consumed-key predicate. -/
structure DurableStore (V : Vocabulary.{w}) where
  root : V.Root
  consumed : NullifierKey V → Bool

/-- The state that a successful commit would install. -/
def DurableStore.install
    {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    [LinearOrder V.Height] [DecidableEq (NullifierKey V)]
    {verifier : FillVerifier U V} {now : V.Height}
    {spec : HoleSpec U V} {advice : Advice spec}
    (store : DurableStore V) (fill : VerifiedFill verifier now spec advice) :
    DurableStore V where
  root := fill.postRoot
  consumed := fun key =>
    if key = spec.nullifierKey then true else store.consumed key

/-- Exhaustive durable commit result.  A refusal carries no replacement store;
therefore only `committed` can mutate durable state. -/
inductive CommitOutcome (V : Vocabulary.{w})
  | committed (next : DurableStore V)
  | stale
  | alreadyConsumed
  | conflict

/-- Tiny compare-and-swap/nullifier transition.  Replay is checked before the
root so a second presentation is classified as replay even though the first
commit may also have changed the root. -/
def commitFill
    {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    [LinearOrder V.Height] [DecidableEq V.Root]
    [DecidableEq (NullifierKey V)]
    {verifier : FillVerifier U V} {now : V.Height}
    {spec : HoleSpec U V} {advice : Advice spec}
    (casConflict : Bool) (store : DurableStore V)
    (fill : VerifiedFill verifier now spec advice) : CommitOutcome V :=
  if store.consumed spec.nullifierKey = true then
    .alreadyConsumed
  else if store.root = spec.preRoot then
    if casConflict = true then
      .conflict
    else
      .committed (store.install fill)
  else
    .stale

/-- Interpret a commit result as durable state.  Every refusal is the identity. -/
def CommitOutcome.storeAfter {V : Vocabulary.{w}}
    (before : DurableStore V) : CommitOutcome V → DurableStore V
  | .committed next => next
  | .stale => before
  | .alreadyConsumed => before
  | .conflict => before

/-- Apply a verification result to the durable boundary.  Non-acceptance never
calls `commitFill`. -/
def settle
    {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    [LinearOrder V.Height] [DecidableEq V.Root]
    [DecidableEq (NullifierKey V)]
    {verifier : FillVerifier U V} {now : V.Height}
    {spec : HoleSpec U V} {advice : Advice spec}
    (casConflict : Bool) (store : DurableStore V) :
    VerifyOutcome verifier now spec advice → DurableStore V
  | .accepted fill => (commitFill casConflict store fill).storeAfter store
  | .rejected _ => store
  | .pending => store
  | .expired => store
  | .unsupported => store
  | .backendUnavailable => store

/-- **Rejection has no durable effect**, including when the rejected outcome
is the result returned by the total verifier. -/
theorem verify_rejected_no_mutation
    {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    [LinearOrder V.Height] [DecidableEq V.Root]
    [DecidableEq (NullifierKey V)]
    {verifier : FillVerifier U V} {now : V.Height}
    {spec : HoleSpec U V} {advice : Advice spec}
    (casConflict : Bool) (store : DurableStore V) (reason : RejectReason)
    (h : verifyFill verifier now spec advice = .rejected reason) :
    settle casConflict store (verifyFill verifier now spec advice) = store := by
  rw [h]
  rfl

/-- **First commit consumes; second commit refuses.**  Starting from the bound
root with a fresh nullifier and no CAS conflict, the first presentation commits
the verifier-computed post-root, while replay of the same verified fill is
classified `alreadyConsumed`. -/
theorem commit_then_replay_refused
    {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    [LinearOrder V.Height] [DecidableEq V.Root]
    [DecidableEq (NullifierKey V)]
    {verifier : FillVerifier U V} {now : V.Height}
    {spec : HoleSpec U V} {advice : Advice spec}
    (store : DurableStore V) (fill : VerifiedFill verifier now spec advice)
    (hfresh : store.consumed spec.nullifierKey = false)
    (hroot : store.root = spec.preRoot) :
    let next := store.install fill
    commitFill false store fill = .committed next ∧
      commitFill false next fill = .alreadyConsumed := by
  dsimp only
  constructor
  · simp [commitFill, hfresh, hroot]
  · simp [commitFill, DurableStore.install]

/-! ## The forbidden strong-hole substitution -/

/-- Deliberately unsafe anti-model: late data is allowed to carry a replacement
specification as well as its value.  This is precisely the strong-hole shape
that the real `Advice spec` rules out. -/
structure UnsafeStrongAdvice
    (U : FirstOrderUniverse.{u, v}) (V : Vocabulary.{w}) where
  replacement : HoleSpec U V
  value : U.El replacement.code

/-- Unsafe substitution discards the original eager shape. -/
def unsafeSubstitute
    {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    (_original : HoleSpec U V) (late : UnsafeStrongAdvice U V) :
    Σ replacement : HoleSpec U V, Advice replacement :=
  ⟨late.replacement, ⟨late.value⟩⟩

/-- **Strong-hole refuter.** Whenever a replacement shape differs, allowing it
in late advice definitionally substitutes that different shape.  The safe
dependent `Advice spec` has no corresponding construction. -/
theorem strong_hole_substitution_refuter
    {U : FirstOrderUniverse.{u, v}} {V : Vocabulary.{w}}
    (original replacement : HoleSpec U V)
    (value : U.El replacement.code) (hne : replacement ≠ original) :
    (unsafeSubstitute original
      ({ replacement := replacement, value := value } : UnsafeStrongAdvice U V)).1 ≠ original := by
  simpa [unsafeSubstitute] using hne

end Minidregg.Theory.GuardedAdvice
