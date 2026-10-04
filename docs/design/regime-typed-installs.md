# How an install is typed: ResearchRegime and agreement evidence

A Generic Simplex agreement certificate orders a change; it does not authorize or physically
install it. This note says how that principle is typed. The pieces are
[Theory/ResearchRegime](../../Theory/ResearchRegime.lean) (a verdict may not outrank the evidence
that settled it) and its one consumer,
[Kernel/AgreementEvidenceRegime](../../Kernel/AgreementEvidenceRegime.lean) (a COMMIT certificate is
a witness for ORDERING, never for AUTHORIZATION; header, `:1-27`).

**Evidence class: compiled, in the opt-in `ResearchWip` library**
(`ResearchWip.lean:99`, `:138`; surface `authored-research`,
`protocol/lean-build-surfaces.json:4067-4070`). Nothing in the default build or the Host
imports either module, so no install is gated by them today; they say how an install
claim must be badged once a deployment renders one.

## The regimes

`Regime` (`Theory/ResearchRegime.lean:72`) is `ballot < optimistic < witness` by
`strength` (`:85`). A verdict settled by **witness** is a realizability fact (some
discharging witness exists); **optimistic** is "upheld unless a refutation is observed in
the window" and costs `RefutationComplete` and `Actuated` hypotheses; **ballot** is an
aggregation of assertions, where Arrow and List and Pettit apply.

A `Publication` (`:244`) carries the claim, the observed refutations, the ballot, the regime
it was `settledIn`, the regime it is `renderedAs` (the badge), the settlement, and the field
`honest : renderedAs.strength ≤ settledIn.strength` (`:257`). The honesty condition is a
structure field, so a badge outranking its evidence cannot be constructed. What it buys:

- `rendered_witness_is_true` (`:265`): an honest publication rendered as witness holds;
  `rendered_optimistic_is_not_refuted` (`:284`).
- The regimes are separate: `unanimous_ballot_upholds_a_refuted_claim` (`:181`: a unanimous
  ballot, a sound refutation actually observed, a genuinely false claim, all at once),
  `witness_does_not_imply_ballot` (`:231`: truth does not win votes), and the one implication
  that holds, `settled_witness_imp_optimistic` (`:120`).
- The field is not decorative: `laundered_publication_can_be_false` (`:308`) drops it and
  exhibits a witness-badged publication of a refuted claim.

## Agreement evidence

`AgreementClaim` (`Kernel/AgreementEvidenceRegime.lean:44`) separates what a joint change can
claim: `ordered context view block` (a quorum COMMIT certificate for exactly this block at this
view of this context exists) and `authorized context block` (the change may be installed).
`certificateVerify` (`:53`) is the regime's verifier over the native certificate type: it accepts
an `ordered` claim when the certificate binds exactly that context, view and block and the native
verdict `accepted` holds (in deployment `acceptedByNative`, `:72`, only certificates whose
canonical bytes are those of a `GenericSimplexIO.VerifiedCommit`); it returns false for every
`authorized` claim.

- `commit_never_witnesses_authorization` (`:95`): no certificate, whatever the native verifier
  accepts, upholds an authorization claim.
- `accepted_certificate_upholds_its_order` (`:104`): an accepted certificate witnesses exactly its
  own order.
- `authorization_never_rendered_as_witness` (`:115`): any honest publication of an authorization
  claim is not rendered as a witness.
- `installByAgreement` (`:151`): the honest typing of "the committee agreed to install": the
  authorization claim, settled by the signer ballot (`signerBallot`, `:143`: carried iff a quorum of
  distinct configured parties signed) and rendered at ballot strength, the strongest badge agreement
  evidence alone licenses.
- Keystones for a concrete quorum-one certificate (`Keystone`, `:172-225`): the witness theorem bites
  (`publication₀_upheld`, `:191`), a different view is not upheld (`other_view_not_upheld`, `:198`),
  and the committee install carries no authorization (`install_by_agreement_carries_no_authorization`,
  `:217`) and cannot be re-badged as a witness (`install_by_agreement_not_witness`, `:223`).

## What this does not say

Nothing here says any regime is sound, nor that a deployment's verdicts are. The witness badge for
an install must come from a different verifier (a typed authorization witness), which does not
exist yet. Consistency between two `ordered` claims is not proved here: it is
`GenericSimplexCertificateSafety.attributed_commit_sends_prefix_consistent` under its own
hypotheses (`LocalFaithful`, `roster.card = 3f + 1`, the fault bound). The `accepted` verdict is an
IO boundary (a quorum of ML-DSA-65 signatures checked by the native verifier), not a proof of
unforgeability.
