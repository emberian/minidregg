# Generic Simplex safety beyond n = 3f + 1

Ledger row: task/12305 (simbi). Lane `lane/quorum-n-ge-3f1-upstream`, built on emberian/minidregg
main `5d607d21d` (a port of akapug `lane/quorum-n-ge-3f1` @ `7bfcc0db`). That first slice changes
Lean proofs only. The second slice (task/12332, below) widens the oracle's `Config.wellFormed` to
`n ≥ 3f + 1`; it changes no Rust and no behaviour at `n = 3f + 1`.

## What changed

The abstract safety chain used to assume `roster.card = 3 * f + 1`, with every
quorum guard at `2f + 1`. It now takes the roster size and three thresholds as
explicit parameters:

- `q` is the VOTE/COMMIT quorum (`Config.quorum = n - f`).
- `c` is the CANDIDATE count that sends a core READY.
- `r` is the READY count that clears a view, by preparing a block or disabling the view.

The relay guards (`f + 1` votes before a CANDIDATE, `f + 1` READYs before a relay READY)
are unchanged.

- `Kernel/GenericSimplexQuorum.lean`
  - `honest_intersection_of_overlap`: an `a`-set and a `b`-set drawn from an
    `n`-roster with `a + b ≥ n + f + 1` share an honest member. This holds for any `n`.
  - `Thresholds n f q c r` (Prop structure) has one field per safety use:
    `n + f + 1 ≤ q + q`, `n + f + 1 ≤ q + c`, and `f + 1 ≤ q, c, r`.
  - Three instances:
    - `thresholds_standard (3f+1 ≤ n)`: the kernel's own guards, `q = n - f` and `c = r = 2f + 1`.
    - `thresholds_legacy (n = 3f+1)`: every threshold is `2f + 1`.
    - `thresholds_small_quorum (3f+1 ≤ n)`: the stretch profile below.
  - `two_f_plus_one_quorum_unsafe_above_legacy` is a concrete counterexample. At `n = 5, f = 1`,
    two `2f+1` sets can meet only in a faulty member. So "keep `2f+1` and drop the
    size premise" was never an option: the VOTE/COMMIT quorum has to grow with `n`.
- `Kernel/GenericSimplexVAInvariant.lean`
  - `LocalFaithfulAt tr roster faulty f q c r` is the old `LocalFaithful` with the
    thresholds as parameters.
  - `LocalFaithful` is now an `abbrev` for the legacy instance `(2f+1, 2f+1, 2f+1)`. Every
    existing constructor and projection site compiles unchanged.
  - Every safety lemma has an `_at` form taking `Thresholds roster.card f q c r`, or only
    the `f + 1 ≤ ·` bounds it actually uses.
- `Kernel/GeneralSimplexReachability.lean`: `known_eq_committed_at`, `committed_not_disabled_at`,
  `known_parent_at`, `committed_ancestor_of_later_at` and `committed_prefix_consistency_at`.
  - `committed_prefix_consistency_admitted` is the headline theorem. It proves committed-prefix
    safety from `3 * f + 1 ≤ roster.card` with the kernel's `n - f` / `2f + 1` guards.
  - `known_zero` is generalized in place.
- `Kernel/GenericSimplexCertificateSafety.lean`
  - `AttributedCommitSendsAt tr roster faulty q view block` is a certificate of `q` signers.
    The old `AttributedCommitSends` is an `abbrev` for `q = 2f + 1`.
  - `EvidenceValueAt` is generalized the same way.
  - Every certificate theorem has an `_at` form, up to `attributed_commit_sends_prefix_consistent_at`
    and `certified_next_record_unique_at`.
- `Kernel/GenericSimplexReceiverSafety.lean`
  - `verifiedCommit_attributed_at` takes the native verifier's own `Config.quorum` signer
    count as the certificate quorum, with NO size premise.
    The certificate names its chain by digest, so `block` is the caller's chain, under the same
    origin and digest premises as upstream's `verifiedCommit_attributed`.
  - `ordered_next_payload_unique_at` is the consumer join for any `Thresholds`. Like upstream's
    `ordered_next_payload_unique`, it takes `leftBlock`/`rightBlock` and the `leftReads`/`rightReads`
    history equalities.

Every old `n = 3f + 1` statement keeps its name and signature. Each is now a one-line
corollary built with `thresholds_legacy size`, or is left unchanged where it never used
`size`. The downstream modules (EngineSafety, ObservationSafety, ActualFaithful, Trail,
SupportExtends, RebaseGhost, AgreementEvidenceRegime, SimplexQualification, Verify) are untouched.

Every new theorem carries `#assert_axioms`. That check fails on `sorryAx`, on a declared
axiom, and on `native_decide`'s compiler trust.

## Which hypotheses were weakened

- `size : roster.card = 3 * f + 1` became `th : Thresholds roster.card f q c r`.
  For the kernel's guards, that is exactly `3 * f + 1 ≤ roster.card` (`thresholds_standard`).
- The certificate quorum `2 * f + 1 ≤ signers.card` became `q ≤ signers.card`.
- The `2f + 1` VOTE/COMMIT support in `LocalFaithful` became `q`. The CANDIDATE→READY
  support became `c`. The READY→prepare/disable support became `r`.

## The oracle and its refinement (lane `lane/quorum-oracle-n-ge-3f1`, task/12332)

This second slice widens the executable oracle and re-proves the refinement layer.

- `Kernel/GenericSimplex.lean` `Config.wellFormed` admits `(faults == 0 && parties == 1) || (0 < faults && 3 * faults + 1 ≤ parties)`
  (was `parties == 3 * faults + 1`). Solo Simplex `(parties = 1, faults = 0)` is preserved because `quorum = 1` and `2f + 1 = 1`
  coincide. For `n > 1`, `faults = 0` is refused: at `faults = 0` and `n = 5`, `2f + 1 = 1` while `quorum = 5`, meaning 1 timeout
  `CANDIDATE(⊥)` would unilaterally disable a view while `COMMIT` demands all 5 votes. For multi-node committees `n > 1`,
  `0 < faults` and `3f + 1 ≤ n` are required.
  `Config.quorum` stays `parties - faults`; every guard of `valueRules`/`argumentRules`/`wantsOut` is unchanged (`n - f`, `2f + 1`, `f + 1`).
  At `n = 3f + 1` the new admission computes the old one (`wellFormed_at_legacy`, proved), so `start`/`step` compute the same
  states there; a config with `n > 3f + 1` (and `f > 0`) used to fail at `start`/`step` and now runs.
- `EmissionSupport.EventSupported` and `GlobalEmission.GlobalEventSupported` record the
  READY-core, READY-prepare and disable supports at `2 * c.faults + 1`, the guard the
  executable reads, instead of `c.quorum`. `argumentRules_invariant` then needs no size,
  and neither do `progressView`/`pass`/`pump`/`step` invariants, `step_emission`,
  `step_readable` or `reachable_emission_invariants`.
- `localFaithful_of_supported`, `actual_local_faithful` and `Trail.good_faithful` prove
  `LocalFaithfulAt … c.quorum (2f+1) (2f+1)` with no size premise. `AuditRefinement.faithful`
  and `RelativeReach.Faithful.rules` carry the same profile.
- `GeneralSimplexReachability.config_thresholds` turns `3f + 1 ≤ n` into `Thresholds` for
  that profile. The `actual_*` safety theorems (`actual_committed_prefix_consistency`,
  `actual_certificates_prefix_consistent`, `actual_certified_next_record_unique`,
  `actual_state_commits_compatible`, `actual_delivered_blocks_compatible`,
  `actual_ordered_next_payload_unique`), `refined_engine_commits_compatible`, the
  `reachable_*` SupportExtends theorems, `ghost_step`, `ghost_rebase` and the
  `RelativeSide`/`RelativeFaithful`/`RelativeAgreement` chain take `3f + 1 ≤ n` instead
  of `n = 3f + 1`. Certificates there are `AttributedCommitSendsAt … c.quorum`, the native
  verifier's own count (`verifiedCommit_attributed_at`).
- `SupportExtends` gains `support_has_honest_vote_at`, `vote_extends_commit_at` and
  `support_extends_commit_at`; the legacy names are corollaries. `LocalFaithfulAt.toLegacy`
  and `config_quorum_legacy` keep the `n = 3f + 1` witness statements
  (`honest_execution_faithful`, `localFaithful_committed_run`) as they were.

## What is still n = 3f + 1 only

- `JumpReach.SettledBelowFrontier`, an unproved statement, keeps its `n = 3f + 1` premise.
  `EventualCommit` reads `wellFormed` and so now ranges over every admitted roster; it is
  unproved as before.
- The legacy abstract theorems (`committed_prefix_consistency`, `verifiedCommit_attributed`,
  `ordered_next_payload_unique`, `local_output_attestations_*`, …) keep their names and
  `n = 3f + 1` signatures; their `_at` forms cover any roster.
- `GenericSimplexReconfig` (churn): `ChurnSafe n f n' f'` (`f' < (n - f) + (n' - f') - (n' - n) - n`)
  simplifies directly to `n > f + 2f'` (`churnSafe_iff`, proved). Under legacy `n = 3f + 1` growing to `f' = f + 1`,
  `f + 2f' = 3f + 2 > n`, so every growth under legacy fails the bound and requires the readiness rule
  (`growth_needs_readiness`). Widening `n` beyond `3f + 1` allows committees satisfying `n > f + 2f'` (e.g. `n ≥ 3f + 3`
  for `f' = f + 1`) to be churn-safe without readiness or state transfer. Full dynamic reconfiguration remains ungeneralized.
- Liveness is proved for no roster size.
- Re-pinning the oracle SHA in clockdag's `crates/mesh-simplex/PROVENANCE.txt` is a separate step.

## Stretch: the smaller quorum q = ⌈(n + f + 1) / 2⌉

`thresholds_small_quorum` proves that this profile satisfies `Thresholds`, so every `_at`
safety theorem applies to it:

- VOTE/COMMIT quorum `q = (n + f + 2) / 2`. At `n = 6, f = 1` that is 4, against 5 for `n - f`.
  At `n = 600, f = 199` it is 400, against 401.
  **Crash resilience trade-off:** Under standard `q = n - f, c = r = 2f + 1`, `(n = 6, f = 1)` tolerates
  only `n - q = 1` crashed node, even if 0 Byzantine faults occur. By contrast, `thresholds_small_quorum`
  (`q = c = 4` at `n = 6, f = 1`) tolerates 2 crashes at 0 Byzantine faults (or 1 Byzantine fault + 1 crash).
- **The CANDIDATE→READY guard must rise** from `2f + 1` to `c = n + f + 1 - q = ⌊(n + f + 1) / 2⌋`.
  That is 4 instead of 3 at `n = 6`, and 400 instead of 399 at `n = 600`. Safety needs
  `q + c ≥ n + f + 1`: a committed block's `q` COMMIT senders must meet any `c` CANDIDATE
  senders in an honest member. Without the raise, the small quorum is unsafe.
- The READY→clear guard may stay at `2f + 1`. Safety needs only `r ≥ f + 1`, and `2f + 1`
  keeps Bracha READY totality.
- The `f + 1` relay guards stay unchanged.
- Liveness is NOT proved, here or anywhere for Generic Simplex in this repo. The informal
  threshold argument holds: honest parties alone reach every guard when `q, c, r ≤ n - f`,
  and `q ≥ 2f + 1` lets a vote quorum's honest voters (at least `q - f ≥ f + 1`) drive every
  honest party to CANDIDATE(x). Both hold for `n ≥ 3f + 1`. A real liveness proof is a
  separate obligation.

## Fabric evidence

All Lean builds ran on the Fabric. None ran on the laptop hub.

- First slice (proofs only), tip `196483847`: `job_ca862d2a921ffc0f59d745e1`, green
  (`build-mini-kernels.sh && lake build` of 42 GenericSimplex/Verify targets). This is the baseline
  of the second slice: `0a3dd1ea8` differs from it only in this file.
- Second slice, tip `3f8d2c293`: `job_49ad6b4e61ede340e73a68b8`, red. `ghost_rebase` still called
  four legacy lemmas; fixed in `c2b145d86`.
- Second slice, tip `c2b145d86`: `job_0876b468f59aec1013a3ba8e`, green (2468 jobs; the 42 targets
  plus `Kernel.GenericSimplex`, `Erasure`, `Window`, `Relative`, `NativeHostContext`,
  `Compiler.GenericSimplexServe`, `Compiler.GenericSimplexIO` and five more `Verify.GenericSimplex*`
  and fixture modules).
- Second slice, tip `a5d81d7c2`: `job_9a51e2dd7d8ca6d282e4d5d0`, `lake build` of every module
  that imports a changed module (382 library modules). Red only in seven targets, all inherited:
  `TokenCensus` and six modules that only the opt-in `ResearchWip` imports
  (`Compiler.PrivateCircuitAllocationFast`, `Compiler.PortableJointCustodyIO`,
  `Kernel.RunComputeActivation`, `Kernel.JointReservationFunding`,
  `Kernel.JointProtectedGateProofs`, `Kernel.RoomReleaseCurrent`). The same seven targets on the
  base `0a3dd1ea8` (`job_f12e374c6521956b4069ef88`) fail with the identical 34 error lines.
- Second slice, tip `a5d81d7c2`: `job_cf6b7f7b947e574481cd2fcd`, the `generic-simplex-harness` and
  `generic-simplex-log-reopen` executables both pass (exit 0).
- Second slice, tip `a5d81d7c2`: `job_c355a45cd66dc4bf5236c74b`, an uncommitted probe runs the
  oracle (`Timed.runUntil`) at `(n, f)` = `(4,1)`, `(5,1)`, `(6,1)`, `(7,2)`, `(10,3)`,
  each with no fault and with member `n - 1` silent. Every run is admitted (quorum `n - f`), every
  live replica commits the block and `timedSafe` holds; `(3,1)` is refused (`start` fails).
