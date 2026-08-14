# Cross-repository contracts — current truth, 2026-08-14

This file is the narrow interface sheet for the receipts-native compute
fabric.  It is not a deployment claim or a second architecture narrative.
`REORIENTATION.md` explains why the boundaries exist; this file says what may
cross them.

All artifacts are neutral data until the receiving layer decodes them,
checks their registered version and source identity, and proves the relation
it owns.  No producer may serialize authority, acceptance, or durability into
existence.

## 1. Preoscript / leanuweave → minidregg

### Planning-data crossing

Use a checked **Projection V3** artifact for rich partial-computation data:
declarations, guarded fields, futures, query/result/certificate rows, selected
plans, escalation actions, and witnessed budgets.

The artifact must carry:

- schema and codec versions;
- stable declaration/session/plan/budget identifiers;
- the exact source/artifact identity;
- canonical bytes and a bounded successful decode/validation result; and
- the selected resource profile and its realized budget evidence.

minidregg may use those values to construct or constrain a request.  It must
independently bind the request kind, subject, target, verb, arguments, effects,
pre-state root, policy, nonce, and cost context.  A plan is never an
authorization witness, scheduling permit, semantic receipt, or proof-system
acceptance bit.

### Context-auth crossing

Use the checked **RuntimeAuth V4 sidecar** only where a runtime crossing needs
context-bound grant/roster/resource facts.  Its decoded manifest remains
neutral.  minidregg must independently validate the context pin, signature or
attestation profile, authority and membership policy, nonce/operation scope,
and exact request binding.

Projection V2 is not the default new crossing.  The independently owned
`Compiler/UwueavePreoProjectionV2.lean` lane must not be merged merely because
its generated Rust data is well formed; first decide whether the consumer
needs V3 planning data or the narrower V4 context sidecar.

## 2. breadstuffs / Dregg2 → Selvage and minidregg

The implementation rail may emit only candidate data and versioned verifier
artifacts.  The minimum proof-suite export is:

```text
ZkmlSuiteArtifact
  source repository + source commit + artifact content identity
  statement/proof/transcript codec versions
  base field modulus and canonical base-field codec
  extension degree, defining polynomial, basis, and extension codec
  Poseidon2 width, rate/capacity, S-box, round schedule
  round-constant and linear-layer canonical data/identity
  leaf/node/domain-separation rules and digest layout
  Merkle arity, leaf packing, path codec, root codec
  protocol id and mode (IR-v2 FRI or BaseFold/RS)
  code rate/domain layout, query count, grinding rule
  exact Fiat--Shamir alphabet and ordering
  checker/controller id, version, and content identity
```

The producer must attach checked meaning to the first-order export and retain
known-answer/refusal vectors.  Selvage must not hand-copy constants, infer a
suite from benchmark fixtures, or treat Rust/Plonky3 verification as its own
theorem.

The first production-rail export is now exact and source owned:

- producer: breadstuffs commit
  `e496fb48d6aaf374d4c0302c95c0fcc69bb8051d`, exporter
  `metatheory/Dregg2/Circuit/ZkmlSuiteArtifact.lean`;
- suite: `dregg.ir2.babybear-ext4.poseidon2-w16.fri.v1`;
- receiver payload:
  `artifacts/zkml-suites/dregg-ir2-babybear-poseidon2-w16-fri-v1.payload.json`,
  6,654 identity bytes excluding its trailing newline, SHA-256
  `b131ed2ad3e9628dbcdbf2bf6c8cf845a6f31f87eea3c91ba8aa00d019c494f0`;
- source envelope: the adjacent `.envelope.json`, pinning the producer commit,
  tree, exporter, Poseidon, FRI-verifier, and Cargo-lock blobs; and
- receiving checks: `scripts/check-zkml-suite-artifact.sh` plus the exact
  admission/refusal theorems in `Selvage/ZkmlSuiteRegistry.lean`.

That is a checked export and fail-closed local identity registry.  The IR-v2
suite identity itself is not an authenticated production registry, a
Rust-to-Lean checker refinement, a Plonky3 soundness theorem, or a BaseFold
suite registration.

Selvage now also consumes the exported Poseidon primitive without maintaining
a second transcription.  `scripts/render-zkml-poseidon2-data.sh` renders the
round constants and source-derived linear columns into
`Selvage/ZkmlPoseidon2Data.lean`; the artifact gate diffs that generated view
against the exact admitted payload.  `Selvage/BaseFoldPoseidon2.lean` gives the
tables BabyBear field semantics and deliberately assigns a distinct local
profile id,
`minidregg.basefold.babybear-ext4.poseidon2-w16.binary-merkle.v1`.  Its leaf is
one actual quartic-field symbol in the proved `[1,X,X^2,X^3]` basis, padded to
one eight-lane rate block with zero capacity; its ordered node is
`left8 || right8` followed by one permutation and truncation.

That local profile is a checked semantic construction, not a claim that the
IR-v2 MMCS already uses this BaseFold leaf, not a registered production wire
suite, and not a collision-resistance or random-oracle theorem.

One native computation response has the shape:

```text
CandidateComputation
  exact request/statement identity
  model and weight identities/roots
  canonical input identity/root
  candidate canonical output bytes/root
  proof bytes or an explicit native error
  selected suite/checker identity
```

Native success means only that bytes were returned.  Decode failure, version
mismatch, wrong request/statement identity, wrong root, checker rejection, or
an unavailable registered suite all fail closed.  Native code never returns
the minidregg acceptance bit.

## 3. Selvage → minidregg

Selvage returns checked evidence about one exact typed statement.  An accepted
evidence object must bind:

- the exact statement and C/A/B commitment roots;
- the contraction claim and claimed output root;
- the exact transcript/checker/suite/codec identities;
- every opening and verifier decision consumed;
- the named algebraic, proximity/query, commitment-collision,
  Fiat--Shamir/ROM, grinding/beacon, and registry terms; and
- the claim ceiling (exact recomputation, interactive IOR, ROM theorem,
  executable checker, or deployment evidence).

The raw BaseFold theorem supplies
`m·3/|F| + (1−τ)^q + Pr[accepted position equivocation]`.  The executable
perfect-binary-tree semantics in `Selvage/BinaryMerkle.lean` now reduce that
last event losslessly to a leaf or ordered-node collision, retaining the FRI
level; `Selvage/BaseFoldPoseidon2.lean` specializes the reduction to the real
quartic carrier and source-derived Poseidon2 profile.  Its fixed leaf is proved
equal to the one-block fragment of Selvage's generic sponge, whose correct
work-indexed ROM target and exact capacity/full-state cardinalities are named
in `Selvage/BaseFoldPoseidon2Rom.lean`.

The remaining deployment legs are the byte-level root/path/Ext4 codec
refinement, collision-game pricing, the work-indexed sponge game, and the
deployed-permutation idealization.  The Tower256/cSHAKE additive-FRI controller
remains a proof pattern, not the zkML suite.

`Selvage/BaseFoldBcsFiatShamir.lean` now fixes the local BaseFold construction
alphabet before any native codec is admitted.  It frames the profile and
statement, every prefix-adaptive root, three-coefficient sumcheck message,
challenge, terminal root, query label/seed, opened Ext4 values, and all three
binary-Merkle paths.  Challenge and query namespaces are distinct; each draw
is a literal Poseidon2 sponge construction query; causality excludes future
frames; primitive work equals absorbed block count; and accepted submitted
paths reflect into `BaseFoldRawCommittedIorAccepts` on the same coherent query
schedule.  Its original modulo decoder remains deterministic but is not a
uniformity claim; the strict path below supplies unbiased sampling.  This
original profile is intentionally still unpadded.  The separate
`BaseFoldBcsPadding` profile proves injective rate-block padding and its exact
`m + queryCount` work delta.  That padded
schedule is now a work-bounded distinguisher and reaches the combined strict
accepted-query/raw-IOR/ROM ledger at its exact larger work argument.  The
adaptive work-space sponge/RO coupling, whole-receipt/Merkle serialization,
and deployed Poseidon2 permutation idealization remain open.

`Selvage/BaseFoldBcsSpongeGame.lean` makes the next boundary explicit rather
than leaving the construction outside the security game.  The exact ordered
challenge/query list is now a `Distinguisher` for any answer verdict, its
worst-case `PrimitiveWorkBound` is exactly the absorbed-block receipt ledger,
and the still-conditional `romConstructionTarget` specializes to the concrete
BaseFold `romError` at that ledger.  The adapter is intentionally indexed by a
fixed candidate receipt; it does not claim the missing online-prover semantics
or adaptive eager/deferred coin-space reindexing.

`Selvage/BaseFoldBcsPadding.lean` supplies a separate `.pad1` construction
identity rather than retroactively changing that receipt schedule.  Appending
its reserved terminal rate block is injective on all block lists; the causal
and domain-separated draw laws survive; and its exact primitive-work delta is
one call per public draw, `m + queryCount` per receipt.  Its work-indexed game
adapter and `strictPaddedAcceptedRawRomLedger` now preserve that larger ledger
through the same joint accepted-query and `q / p` terms.  This is not yet a
whole receipt codec: `BaseFoldBcsByteCodec` now supplies strict canonical
field/rate bytes and a lawful complete padded-message codec, while Ext4 values,
roots, paths, receipt framing, and native refinement remain to be composed.

`Selvage/BaseFoldBcsByteCodec.lean` fixes one BabyBear value as four
little-endian bytes and refuses any decoded word at or above the modulus.  The
actual construction rate is eight lanes, not twelve: the lawful lane-major
rate codec therefore consumes exactly 32 bytes, rejects trailing bytes, and
round-trips injectively.  Encoding the `.pad1` message costs exactly
`32 * (semantic blocks + 1)` bytes.  Its lawful whole-message decoder accepts
only complete rate blocks and the reserved terminal block, refusing leftovers
and missing or different terminals.  This is the canonical Lean wire meaning;
no handwritten native routine is treated as refined by implication.

`Selvage/BaseFoldBcsRunSchedule.lean` carries the same padded receipt into the
actual work-indexed deferred runner.  For a fixed receipt, public query choice
depends only on answer-list length, so the per-round primitive segments are a
static nonempty partition whose terminal boundary is the existing ROM work
ledger.  A full deferred run on exactly that vector cannot exhaust: it returns
one answer per draw, consumes the entire vector, and leaves no suffix.  The
segment heads and eager full-message coordinates induce explicit swaps; those
swaps compose into an actual equivalence of the entire work-vector space and
preserve its uniform counting measure exactly.  When
`queryCount ≤ BabyBearExt4.modulus`, the entire padded public-message family is
proved prefix-free: distinct causal challenges diverge at padding versus the
next challenge-result frame, challenge/query domains differ in their first
block, and bounded query labels are injective.  This closes the structural
full-message routing premise for every such fixed receipt.  The remaining
sponge/RO crossing requires composed eager/deferred state agreement away from
the already named simulator bad events, followed by the random-
permutation/function and deployed-Poseidon idealization hops.  Exact
committed-source run
`E-20260814T114514-93029-persvati-7e9ab47c9053-lake` built the complete target
in 2,250 jobs with command and source-integrity exits zero.

The same exact ledger now classifies the eager work-stream run sharply.  Every
successful prefix has the fixed answer length, cumulative work boundary, and
remaining suffix already proved for the deferred schedule.  A complete eager
run therefore either consumes the whole vector with exact terminal counters or
fails only as `PrefixHybridError.constructionMismatch`; exhaustion, malformed
segmentation, wrong shape, and wrong count cannot occur.  This does not yet
identify successful eager answers with the deferred answers: a reused
primitive edge may ignore the current final rate coin.  The live semantic
premise is precisely collision-free/fresh-path execution, under which each
eager full-message answer must use the segment-last rate coin moved to the
deferred segment head.  The last coordinate clause is no longer merely a
per-round observation: the complete composed reindex is proved to preserve the
transport for every round because earlier segments fix its last coordinate and
later segments fix its head.  Exact committed-source run
`E-20260814T115938-94384-persvati-7ba4e6cc8f14-lake` built the target in 2,250
jobs with command and source-integrity exits zero.

`Selvage/BaseFoldBcsQuerySampling.lean` supplies the strict uniform query path
without pretending the original modulo decoder was unbiased.  For query
domains of at most 28 bits it rejects the single zero BabyBear element and
uses the exact factorization of `p - 1` to identify every accepted seed with a
slack coordinate and one query coordinate.  Equal fibres give exact uniform
marginals; rejection across `q` independent uniform seed digests costs at most
`q / 2013265921`.  Strict acceptance fails closed on rejection and reflects to
the raw committed-IOR event on that exact schedule.

`Selvage/BaseFoldBcsQuerySamplingJoint.lean` proves the missing whole-batch
statement: accepted digest families are bijective to all unused digest lanes,
all slack coordinates, and one complete query-coordinate vector.  Exact
marginalization makes that vector jointly uniform while retaining the
algebraic challenge vector as context, so the accepted strict schedule feeds
the raw committed-IOR soundness theorem without a coordinatewise-independence
shortcut.  `Selvage/BaseFoldBcsStrictRomLedger.lean` then exposes one additive
ledger containing the raw algebraic term, coherent query miss, retained Merkle
equivocation, exact receipt work-indexed sponge advantage, and
`q / 2013265921` rejection loss.  This is still conditional on the explicitly
open ideal-permutation sponge target; it does not assert deployed Poseidon2
security.  No retry exists in the current semantics, and any future retry rule
must be separately introduced and priced.  Exact committed-source run
`E-20260814T095239-27653-persvati-9a4ab1c91bab-lake` built the combined seam in
2,241 jobs with command and source-integrity exits zero.

The generic reindexing half is now narrower and machine checked in rooted
`Selvage/SpongeIndiffAdaptiveCoupling.lean`: a decision depending only on an
observed prefix may guard swaps wholly inside the unseen suffix, and any finite
program of those guarded swaps is one bijection of the complete fixed work
space.  Supplying pointwise eager/deferred agreement under that program yields
the exact uniform-probability coupling.  What remains is run-specific rather
than measure-theoretic: connect the landed BaseFold segment program and
prefix-free public schedule to the actual sponge construction/reveal steps,
then prove their off-bad public-state agreement.  The
focused seam is green as
`E-20260814T085015-69502-persvati-cdb76138c078-lake` (3,070 jobs), and the same
source commit passed the complete 8,928-job `lake build Minidregg` on hbox as
`E-20260814T085014-69503-hbox-cdb76138c078-lake`; command and source-integrity
exits were zero in both runs.

Evidence does not authorize a request.  minidregg admits it only under the
request-indexed disclosure/audit policy of the same `CommittedTurn` whose
authority, effects, pre-state, post-state, and delta it already owns.

## 4. minidregg → durable history

Only a semantically accepted turn may produce the durable envelope.  The
envelope must bind:

- transaction id and exact request identity;
- canonical result bytes and their post-state root;
- read guards, writes, nullifiers, and exact charge;
- versioned receipt/audit event bytes; and
- the exact replay identity.

Install is atomic at the logical model.  An identical retry is replay; the
same transaction id with changed result or audit bytes is conflict.  These
facts do not prove SQLite, FFI, filesystem, fsync, stable media, power-loss,
replication, consensus, or liveness.  Each physical adapter needs its own
refinement statement and evidence.

The exact matmul slice now instantiates the intermediate framed-WAL boundary in
`Assurance/ZkmlMatmulFramedWal.lean`.  Its one admitted v1 record contains the
transaction, output write, checker-derived output bytes, and audit bytes under
distinct magic/version/checksum framing.  It proves old-state recovery before
sync, exact atomic recovery after the abstract sync barrier, preservation under
a torn successor, cold-start replay, corrupt-frame refusal, stale-root refusal,
and the generic device-to-logical-protocol simulation.  This closes the closed
fixture's use of the existing device model; it does not supply a general
serializer, authenticated codec registry, or refinement from actual OS/storage
operations to `DeviceStep`.

## 5. zkml-research → engineering decisions

Research verdicts are decision inputs, never runtime inputs.  A promoted
decision must name the verdict commit, underlying source/measurement commits,
measurement unit, security regime, and any withdrawn/conjectural premise.

Current pins:

- production-shaped IR-v2: BabyBear, Ext4, Poseidon2-w16, FRI,
  `(log_blowup, queries, grind) = (6,19,16)`;
- its query column is 34 UDR / 73 JBR / 130 withdrawn-CBR bits;
- after repairing the upstream FRI bit-reversal bug, all twelve descriptors
  self-verify at `(2,57,16)`, but the configuration flip was deliberately not
  landed: it divides measured prover work by about 15.19 but costs 2.28 times
  verifier work, 2.4 times more wire, a 16-times larger row ceiling, and 20
  additional UDR bits; it also requires a recursion-verifier `num_queries` pin
  first; and
- the selected multilinear research route is BaseFold/RS in the unconditional
  `(1−ρ)/3` regime, eventually instantiated over the intended zkML
  extension-field/Poseidon2 suite.

## 6. First end-to-end target

The target remains one authorized audited linear-layer turn:

```text
checked Preoscript planning data
  → exact minidregg request and authorization
  → breadstuffs candidate output/proof bytes
  → versioned Selvage checker and explicit failure ledger
  → exact semantic post-state/effects/receipt
  → atomic durable envelope, reopen, and tamper refusal
```

`Assurance/ZkmlMatmulAuditTurn.lean` is the landed semantic floor: exact tiny
recomputation, authorized evidence disclosure, canonical logical install,
history append, replay, and adjacent refusal.  It now routes one versioned
neutral byte envelope through `Assurance/ZkmlMatmulChecker.lean`: wrong output,
suite, planning-artifact id, field encoding, length, and trailing bytes refuse;
the successful branch constructs the contraction equality consumed by the
audit evidence.  Planning-artifact and native-request identities are bound
into the durable audit envelope but grant no authority.

The slice still does not consume an actual V3/V4 decoded artifact or native
runner response, a succinct checker/proof, an authenticated upgradeable
registry, a general production state/WAL codec, or an actual physical store.
Its closed framed-WAL witness reaches the abstract device boundary but not an
OS/filesystem adapter.  The production-rail suite artifact is admitted, but
the toy checker remains F7 exact recomputation and does not accept IR-v2 or
BaseFold proof bytes.  Those crossings should replace its fixtures one at a
time without weakening its request binding or refusal teeth.
