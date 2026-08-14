# Reorientation — 2026-08-14

This is a thin cross-repository orientation note, not another evidence ledger.
`CROSS_REPO_CONTRACTS.md` is the companion boundary sheet.
For research conclusions, `~/dev/zkml-research/docs/VERDICTS.md` is the single
current-truth file.  For exact proof/build evidence, use each repository's own
ledger at the commit being claimed.

Snapshot inspected while writing this note (and refreshed through the strict
BaseFold query-sampling convergence):

- `minidregg` proof snapshot `9a4ab1c91bab` on `main`, with an independently owned Uwueave
  Projection-V2/generated-Rust lane still active in the shared worktree;
- `zkml-research` `bc075dbed6d1` on `dev`, with `vendor/` untracked; its decisive
  blowup-2 verdict is at `97c0b08af1fa`;
- `leanuweave` `0eb9fc15def2` on `dev`, with active durable-artifact,
  runtime-auth-V4, debt-gate, and Rust persistence work; and
- `breadstuffs` `010201bb0d45` on `main`, with independently active field-op,
  PoW, FHE, and measurement work in its shared worktree.

The snapshot is an ownership marker, not a claim that later commits are stale.

## Current convergence truth

The first linear-layer proof seam is no longer at the architectural-sketch
stage:

- the matrix statement is contraction, not Hadamard product, with the corrected
  `(μ+ν)/|F| + κ·3/|F|` soundness account and a native conformance prover;
- the C/A/B multilinear evaluation claims are each tied to their own vector
  commitment root; the transcript account now honestly says three unpriced MLE
  proofs rather than two nonexistent openings;
- the reusable quadratic sumcheck and BaseFold equality braid are proved;
- sumcheck now has a native WARP `Reduction`, `KStateFn`, and
  `RbrKnowledgeSoundness` instance with exact per-round price `d/|F|`;
- BaseFold instantiates that object at degree two, with an inhabited F5 state
  and exact `2/5` round price; and
- the full-word BaseFold IOR verifier checks degree bounds, Boolean recurrences,
  RS descent, and the braided terminal on one challenge vector.  It has perfect
  completeness, exact-codeword wrong-value soundness `m·2/|F|`, and arbitrary-
  word strict-claim soundness `m·3/|F|`;
- the committed BaseFold verifier now commits every prefix-adaptive derived
  fold, authenticates three-symbol sampled fibres, shares the algebraic
  challenge stream with the degree-two sumcheck, and has end-to-end interactive
  completeness;
- coherent power-of-two query paths now give the exact pre-cryptographic bound
  `m·3/|F| + (1−τ)^q`, with no extra round factor on the query-miss term.  The
  theorem keeps the finite-domain quantization premise
  `τ ≤ 1/|level_(j+1)|` explicit rather than silently choosing a deployment
  rate; and
- each of the three matmul MLE claims now has its own arbitrary-word BaseFold
  opening price.  Their additive opening envelope is
  `2(μ+κ+ν)·3/|F|`; the contraction sumcheck's `κ·3/|F|` remains a separate
  algebraic term and must not be counted as an opening;
- the raw BaseFold verifier now proves the corresponding top-level disjunction:
  ideal algebraic acceptance or a retained concrete position-equivocation
  event.  Its coherent bound is
  `m·3/|F| + (1−τ)^q + Pr[accepted equivocation]`; and
- the retained raw equivocation now enters an executable perfect binary tree
  on the canonical LSB-first `Fin (2^k)` index.  Honest paths reconstruct the
  root, wrong path lengths fail closed, and two accepted different values at
  one root/index expose an exact leaf or ordered-node collision at a retained
  FRI level; and
- the production IR-v2 suite now has a checked source-owned first-order export
  at breadstuffs commit `e496fb48d6aaf374d4c0302c95c0fcc69bb8051d`.
  `Dregg2/Circuit/ZkmlSuiteArtifact.lean` derives the Poseidon2 round constants
  and both linear maps from the source definitions, pins the exact Plonky3
  revision and wire codec, and emits the 6,654-byte payload whose SHA-256 is
  `b131ed2ad3e9628dbcdbf2bf6c8cf845a6f31f87eea3c91ba8aa00d019c494f0`.
  minidregg retains that payload and its source-blob envelope under
  `artifacts/zkml-suites`, checks them in the repository trust gate, and admits
  only the exact source/payload/protocol/checker tuple through
  `Selvage/ZkmlSuiteRegistry.lean`.  Unknown suite, changed source, changed
  payload, and changed checker identities are refusal theorems.  This closes
  first-order suite identity, not native-verifier refinement or cryptographic
  soundness.  Exact committed-source persvati runs at minidregg commit
  `521b2eedbd24b6cfceb6a7d35cfb218b03567ed4` built the registry in 460 jobs
  (`E-20260814T070002-31460-persvati-521b2eedbd24-lake`) and checked the payload
  and envelope (`E-20260814T070029-31799-persvati-521b2eedbd24-bash`), with
  runner, command, and source-integrity exits zero in both runs.
- minidregg no longer hand-maintains a second Poseidon transcription:
  `scripts/render-zkml-poseidon2-data.sh` renders the admitted constants and
  source-derived linear columns, and the repository trust gate diffs the
  committed Lean view against the exact payload.  The resulting BabyBear
  evaluator uses the checked round schedule and gives BaseFold a deliberately
  distinct local profile id with one Ext4 power-basis symbol per fixed leaf.
  Its raw FRI equivocation theorem now ends in that profile's concrete
  leaf-or-node collision event.  The fixed leaf is also proved equal to the
  single-block, zero-IV fragment of Selvage's existing sponge semantics; the
  correct unrestricted ROM target remains the work-indexed game, with capacity
  `2013265921^8` and full state `2013265921^16` exposed exactly.  Exact
  committed-source persvati run
  `E-20260814T073709-84456-persvati-3d5795e0b3bc-lake` built the complete
  construction/ROM boundary in 2,236 jobs, and hbox run
  `E-20260814T072652-62290-hbox-ddf61fcb1a57-bash` checked the generated
  payload view; command and source-integrity exits were zero in both runs.

- `Selvage/BaseFoldBcsFiatShamir.lean` now supplies the missing local
  construction alphabet.  A statement-first transcript frames every level
  root, three-coefficient sumcheck message, prior challenge, terminal root,
  query label/seed, opened value, and complete binary-Merkle path.  Challenge
  and query draws use distinct in-band domains and are literal multi-block
  `SpQuery.constr` calls to the source-derived Poseidon2 sponge.  Causality is
  a theorem, Ext4 output decoding round-trips the proved power basis, and total
  primitive work is the exact sum of absorbed blocks rather than the number of
  public draws.  The construction verifier binds its roots and actual submitted
  paths, then reflects into the existing raw committed-IOR event on the same
  coherent schedule.  Exact committed-source persvati run
  `E-20260814T081149-38055-persvati-aa48aaacb40a-lake` built the target in
  2,237 jobs with command and source-integrity exits zero.  Its original modulo
  decoder remains a deterministic construction primitive, not a uniformity
  claim; the strict verifier path below supplies the exact uniform sampler.

- `Selvage/BaseFoldBcsSpongeGame.lean` now places that exact ordered receipt
  schedule inside the `Distinguisher` type quantified by the work-indexed
  sponge game.  For every Boolean verdict and every hypothetical answer trace,
  its primitive work is proved equal to `transcriptPrimitiveWork`; the named
  BaseFold ROM target therefore specializes directly to `romError` at that
  exact ledger.  This is a receipt-indexed game adapter, not an online-prover
  model: producing each next round from returned challenges and the adaptive
  whole-work-space eager/deferred coupling are still open.  Exact
  committed-source persvati run
  `E-20260814T083721-54109-persvati-3702141b42c8-lake` built the adapter and
  conditional ROM specialization in 2,238 jobs with command and
  source-integrity exits zero.

- `Selvage/BaseFoldBcsPadding.lean` now defines a distinct `.pad1` rate-block
  profile instead of silently changing the proved unpadded transcript.  It
  appends one reserved terminal block, proves that transformation injective on
  arbitrary block lists, preserves the causal prefix and challenge/query
  domain laws, and instantiates literal padded construction queries.  Its
  exact receipt cost is `transcriptPrimitiveWork + m + queryCount`: one added
  permutation call per public draw.  The padded schedule is now itself a
  work-bounded `Distinguisher`; `strictPaddedAcceptedRawRomLedger` carries it
  through the accepted joint-query/raw-IOR/ROM ledger with the larger exact
  work argument and the same explicit `q / p` rejection term.  Canonical byte
  packing/decoding is supplied by the adjacent byte-codec seam.  Exact
  committed-source persvati run
  `E-20260814T101425-61974-persvati-d3a92414d682-lake` built the composed
  target in 2,243 jobs with command and source-integrity exits zero.

- `Selvage/BaseFoldBcsByteCodec.lean` pins the canonical bytes immediately
  below that profile.  BabyBear values use exactly four little-endian bytes;
  decoding refuses the modulus and every larger 32-bit word instead of
  reducing it.  The Poseidon2 construction rate is correctly eight lanes, so
  its lane-major codec is exactly 32 bytes, round-trips as a `LawfulCodec`,
  rejects trailing bytes, and is injective.  The whole padded block stream also
  round-trips through a `LawfulCodec`: decoding consumes only complete 32-byte
  blocks, refuses any leftover suffix, and requires the reserved terminal
  block.  A padded block message occupies exactly `32 * (blocks + 1)` bytes.
  The first draft's mistaken
  12-lane/48-byte assumption was caught by the type before landing as a wire
  identity.  Exact committed-source persvati run
  `E-20260814T103404-80410-persvati-c007bcf1dee1-lake` built the target in
  3,020 jobs with command and source-integrity exits zero.  Whole receipt,
  Ext4, root/path, and native-code refinement remain separate crossings.

- `Selvage/BaseFoldBcsQuerySampling.lean` now gives the strict verifier path an
  unbiased query construction.  For every level with at most 28 index bits it
  proves `BabyBear.modulus - 1` factors as an exact slack coordinate times the
  query domain, rejects the lone zero field element, and decodes the remaining
  field elements through an explicit product equivalence.  Every coordinate
  therefore has the same fibre cardinality.  The strict schedule fails closed
  on any rejected seed, reflects acceptance into the existing raw
  committed-IOR event, and exposes the exact rejection price
  `q / 2013265921` for `q` independent uniform seed digests.  It deliberately
  assumes no retry policy: the remaining full-ROM ledger must carry this term
  and any future retry rule explicitly.  Exact committed-source persvati run
  `E-20260814T092057-4803-persvati-15e846c31269-lake` built the final sampler
  in 2,238 jobs with command and source-integrity exits zero.

- `Selvage/BaseFoldBcsQuerySamplingJoint.lean` lifts that single-coordinate
  result to the whole accepted digest family.  One exact equivalence retains
  all seven unused lanes per digest, the factorization slack, and every query
  coordinate; after marginalizing only the nuisance coordinates, the complete
  query vector is jointly uniform even with the algebraic challenge vector
  kept as independent context.  That law now transports the accepted strict
  schedule directly into the raw committed-IOR theorem.  Finally,
  `Selvage/BaseFoldBcsStrictRomLedger.lean` composes the raw algebraic/query/
  equivocation terms with the exact receipt work-indexed sponge advantage and
  `q / 2013265921` rejection term.  The result remains conditional on the open
  ideal-permutation sponge target and does not idealize deployed Poseidon2.
  Exact committed-source persvati run
  `E-20260814T095239-27653-persvati-9a4ab1c91bab-lake` built the combined seam
  in 2,241 jobs with command and source-integrity exits zero.

- `Selvage/SpongeIndiffAdaptiveCoupling.lean` had existed outside the rooted
  build and contained latent failures.  It is now rooted and green.  A
  `WorkPrefixMeasurable` guard provably survives any swap wholly after its
  observation boundary; finite sequences of such guarded swaps compose into
  one equivalence of the complete fixed work-vector space; and pointwise
  eager/deferred agreement under that program produces the exact
  `UniformWorkCoupling` and probability equality.  This closes generic global
  reindex composition, not the run-specific schedule: deriving the guarded
  moves from the actual adaptive sponge transcript and proving off-bad
  eager/deferred agreement remain open.  Exact committed-source persvati run
  `E-20260814T085015-69502-persvati-cdb76138c078-lake` built the focused seam
  in 3,070 jobs, and the exact same source commit passed the complete
  `lake build Minidregg` on hbox in 8,928 jobs as
  `E-20260814T085014-69503-hbox-cdb76138c078-lake`; command and
  source-integrity exits were zero in both runs.

There is also now one deliberately tiny semantic floor in
`Assurance/ZkmlMatmulAuditTurn.lean`.  A fixed 2-by-2 F7 contraction has exact
output, three root-bound MLE claims, an accepted contraction sumcheck, and its
explicitly useless toy BaseFold budget carried as evidence on the same exact
authorized `CommittedTurn`.  Its four canonical result bytes and versioned
audit identity install atomically through `DurableDataIntent`; retry reopens
the identical envelope and altered audit bytes conflict.  The turn now first
routes a canonical candidate envelope through a runnable versioned Lean byte
checker.  The checked branch binds suite/checker/statement, planning-artifact,
native-request, both operand matrices, and output; wrong output, wrong suite,
wrong plan, noncanonical F7 bytes, wrong length, and trailing bytes refuse.
Its installed output is literally the accepted candidate suffix.  Exact
committed-source persvati run
`E-20260814T074351-99292-persvati-a7fe546c8834-lake` built the integrated target
in 3,007 jobs with runner, command, and source-integrity exits zero.

`Assurance/ZkmlMatmulFramedWal.lean` now takes the same checked turn across the
existing physical-boundary model.  Its closed v1 payload exposes the exact
transaction, root-bound output write, four checker-derived output bytes, and
audit bytes inside a distinct versioned/checksummed frame.  The one admitted
record round-trips; a pre-sync tear recovers the old checkpoint; the abstract
sync barrier recovers the exact atomic install; a torn successor preserves it;
cold-start retry replays; corrupt checksum and stale-root sync refuse.  The
generic device simulation is instantiated rather than replaced.  Exact
committed-source persvati run
`E-20260814T075319-12919-persvati-39220a41cf8f-lake` built the target in 3,010
jobs with runner, command, and source-integrity exits zero.  This is still a
closed codec witness and abstract `DeviceStep`, not a general serializer or a
POSIX/filesystem/stable-media theorem.

That floor is exact recomputation, not the final succinct/deployment slice.
The remaining boundary is therefore narrower and more concrete:

1. **`[COMMIT-CR]`:** the field-level binary Merkle construction and retained
   collision reduction are now instantiated.  Pin the deployed root/path/Ext4
   byte codecs to these semantics and price the resulting Poseidon leaf/node
   collision games and byte/work costs;
2. **BCS/Fiat--Shamir:** the exact construction alphabet, causal draw schedule,
   submitted-opening reflection, primitive-work ledger, and strict unbiased
   query sampler are now landed; the complete accepted query family is jointly
   uniform, and the explicit `q / p` rejection loss is carried through the
   raw-IOR/ROM ledger, including the distinct injectively padded rate-block
   profile and its exact work delta.  Derive the run-specific adaptive
   eager/deferred work-space coupling, extend the lawful field/rate bytes to
   the whole receipt and Merkle paths, and perform the deployed-Poseidon
   idealization with its hash/grinding terms visible.  The current policy has
   no retry; any future retry rule must be introduced and priced explicitly;
3. **succinct matmul composition:** the toy serialized statement and
   proof-bearing exact checker are now runnable.  Replace its F7 recomputation
   payload with a checker that binds the C/A/B openings, contraction
   transcript, registered BaseFold suite, and complete named failure budget;
   and
4. **real crossings:** bind the selected Preoscript plan artifact and native
   candidate/proof bytes to that exact request without granting either
   authority, then replace the four-byte fixture and closed one-record WAL
   codec/list registry with general versioned deployed codecs, authenticated
   policy, and an actual I/O-to-`DeviceStep` persistence refinement whose claim
   ceiling stays explicit.

`HalfThresholdFriTranscript` owns the raw opened-fibre/equivocation split;
`HalfThresholdFriQuery` and `HalfThresholdFriCoherent` own the adaptive and
coherent sampled bounds.  Reuse them.  `Assurance/TwoRegimeQueryBudget.lean` is
now landed: for the current IRv2 regime it reports 34/73/130 bits under the
UDR/JBR/withdrawn-CBR models respectively, so only the withdrawn model reaches
128 bits.  This is configuration evidence and a refusal tooth, not permission
to promote the withdrawn assumption into a cryptographic claim.

## One system, five responsibilities

The project is a **receipts-native compute fabric**: every accepted turn is a
typed, authorized semantic state transition whose evidence is carried now or
committed for a precisely priced audit later.

The repositories/layers have different authority:

1. **Uwueave / Preoscript chooses the coordination shape.** It describes
   partial results, guarded data, futures, CRDT-safe work, escalation seams,
   plans, and budgets. Its projections are checked planning data. They are not
   authorization, a scheduling permit, or semantic acceptance.
2. **minidregg owns meaning.** The kernel owns the exact request, authority,
   pre-state, effect, resource law, canonical post-state, receipt, and history.
   Native code may propose bytes or fail; it never returns the acceptance bit.
3. **Selvage owns proof/audit compilation.** It connects round-by-round
   protocol claims to commitments, Fiat--Shamir/BCS, accumulation, sampling,
   and explicit failure budgets. A green theorem is useful only when its
   carriers run and its cryptographic/deployment legs are named or inhabited.
4. **zkml-research owns protocol selection by evidence.** It measures candidate
   designs, records refutations, and decides which statements are worth moving
   into the checked stack. It is not a second semantic kernel or proof tree.
5. **breadstuffs / Dregg2 owns the current implementation rail.** It contains
   the deployed IR-v2 compiler/prover, Lean-authored Poseidon2/AIR artifacts,
   and operational measurement instruments. It may emit a versioned statement,
   candidate result, proof, or verifier artifact. It does not authorize a
   minidregg request or assign semantic meaning to acceptance.

The narrow interfaces should therefore be:

```text
Preoscript checked plan/data
          |
          v
minidregg exact request + authority + state transition
          |
          v
typed computation statement + canonical commitments/openings
          |
          v
breadstuffs candidate/proof bytes + versioned suite artifacts
          |
          v
Selvage proof or commit-and-audit check/evidence
          |
          v
minidregg receipt + durable causal history
```

Every crossing must pin a format/version, source identity, and exact claim
ceiling. No crossing may silently promote data into authority or a host test
into semantic/cryptographic evidence.

## Two proof rails that must not be blurred

The current production-shaped IR-v2 rail and the new multilinear rail share
semantic statements, but they are not one cryptographic suite:

- **IR-v2 today** is BabyBear, Ext4 challenges, Poseidon2 width 16, and the
  existing Plonky3 FRI.  Its deployed `(log_blowup, queries, grind) =
  (6,19,16)` query column is only 34 UDR bits.  The research tree has now
  repaired the upstream FRI bit-reversal bug and made all twelve descriptors
  self-verify at `(2,57,16)`.  The configuration flip was deliberately not
  landed: measurements divide prover work by roughly 15.19 but cost 2.28 times
  more verifier work, 2.4 times more wire, a 16-times larger row
  ceiling, and 20 additional UDR bits.  The production pin remains
  `(6,19,16)`, and the recursion verifier must first pin `num_queries` instead
  of reading the security parameter from the child proof.
- **Selvage's multilinear candidate** is BaseFold over Reed--Solomon in the
  unconditional `(1−ρ)/3` band.  Its deployment target must use the selected
  zkML field/extension and Poseidon2 commitment encoding (or explicitly choose
  and register another suite).  The existing Tower256/cSHAKE additive-FRI raw
  controller is a valuable implementation and reduction pattern, not a
  drop-in zkML PCS instance.

The Poseidon2 constants, matrices, round schedule, narrow/wide AIR artifacts,
and current Plonky3 transcript semantics live in breadstuffs/Dregg2.  The
content/version-pinned first-order export and checked meaning theorem now exist,
and minidregg consumes their exact identity without hand-copying constants.
The field half of the BaseFold boundary is concrete:
`Selvage/BabyBearExt4.lean` proves `X^4-11` irreducible over BabyBear by checked
Euler witnesses and a quadratic-tower norm argument, constructs the quotient
field, proves its finrank is four and its generator satisfies `u^4=11`, and
exposes its canonical four-coordinate power basis.  Exact committed-source run
`E-20260814T070954-42349-persvati-815063f47f38-lake` built it on persvati in
1,944 jobs with command and source-integrity exits zero.  The construction half
is now concrete as well: generated source-owned Poseidon2 data feeds the actual
field evaluator, the separately named Ext4 BaseFold leaf/node profile, and the
binary-Merkle reduction.  What remains is deployment refinement and pricing:
wire codecs, native checker correspondence, leaf/node CR, the work-indexed
sponge game, and the deployed-permutation idealization.

The exact audit turn is deliberately below this fork: it can eventually carry
either suite's accepted evidence, but today it carries exact-recompute Lean
evidence and therefore authorizes neither cryptographic rail by implication.

## First vertical slice

Build **one authorized, audited exact linear-layer turn** end to end.

The slice binds one model/version and real field encoding, one typed input and
claimed output, one contraction statement, one audit/proof policy, and one
resource/disclosure plan. Preoscript supplies checked planning and escalation
data; minidregg authorizes the exact request and derives the receipt; the zkML
relation supplies the exact matmul/contraction semantics; Selvage supplies the
opening/checker and composed audit budget; the durable path appends and reopens
the same canonical receipt.

The success criterion is deliberately narrow:

- the exact accepted computation is stated in Lean and has positive and
  adjacent-refusal witnesses;
- native execution returns only candidate data/proof bytes or an error;
- model/weight binding uses a proof-openable Poseidon2 field encoding and
  layout, not a host SHA checksum described as a registry commitment;
- the checker, commitment binding, beacon/grinding, and Fiat--Shamir terms are
  instantiated or remain explicit zero-suite deployment blockers;
- the Preoscript artifact is consumed as plan data and rebound to the kernel's
  exact request rather than trusted as a permit;
- the receipt survives the existing durable reopen/retry path; and
- exact committed-source verification runs remotely on hbox or persvati, not
  as a large build on nextop.

This is not yet a claim about a whole neural network, correct backpropagation,
PQ-128 FHE, physical stable media, or production key custody.

The current landed floor satisfies the exact Lean computation,
request-indexed authorization, audit-evidence carriage, canonical logical
install, history append, exact replay, and adjacent output/audit-tamper refusal
parts.  It does **not** yet consume the Preoscript artifact or native candidate,
does not serialize/run a succinct BaseFold checker, and uses a toy field,
fixture state codec, local list registry, and logical durability model.  Those
are the next crossings, not footnotes.

## Immediate convergence order

1. Preserve the now-landed contraction statement/native conformance seam and
   its explicit padding, PCS, Fiat--Shamir, and registry residuals.
2. Replace the accidental Projection-V2 bridge decision with an explicit
   interface choice. Use V3 for rich checked plan/result/certificate data;
   use the V4 sidecar only where context-bound runtime-auth facts are actually
   required. In both cases the imported value remains neutral data.
3. Continue from the now-landed raw `OpeningScheme` theorem, flat-hash
   collision witness, and source-owned IR-v2 suite export: instantiate the
   intended BabyBear-extension/Poseidon2 Merkle suite and discharge its
   retained equivocation branch there. Reuse the existing commitment, BCS,
   RBR-to-Fiat--Shamir, and ROM abstractions and the Tower256 raw controller's
   reduction pattern; do not relabel that cSHAKE/Tower256 suite as the zkML
   deployment or invent a KZG-shaped PCS abstraction merely to look
   multilinear.
4. Serialize the exact **BaseFold** verifier alphabet and replace the
   exact-audit evidence with a runnable checker binding the three matmul openings,
   contraction claim, registry entry, checker version, and complete named
   failure budget into one statement. Then instantiate the audit checker's
   transport obligations and real beacon term.
5. Reuse the landed authorized/durable audit turn as the semantic target: bind
   the Preoscript plan and native result/proof bytes into it as neutral inputs,
   replace its fixture codec/registry/durability assumptions one at a time, and
   keep exact replay and tamper refusal green. Only after this is green should
   the slice widen to nonlinearities, multiple layers, low-rank training
   deltas, or encrypted computation.

## Things to stop doing for now

- Do not add generic kernel breadth unless the vertical slice consumes it.
- Do not extend the proof-theory cone merely because another clean theorem is
  reachable; prioritize the runnable commitment/checker seam.
- Do not put Plonky3 in the trust path. Its upstream bug fix is still useful
  for differential measurement and for repairing our stale refusal gate.
- Do not migrate to KoalaBear on the current evidence. Keep BabyBear/Ext4 and
  fix the blowup/query configuration honestly.
- Do not start full vFHE integration before the parameter/PQ-security and
  checker-instantiation questions are settled.
- Do not claim the rank-1 gradient check verifies backpropagated `delta`, or
  that it removes the quadratic commitment to a materialized updated matrix.
- Do not treat V2/V3/V4 projection bytes, Rust tests, SQLite/WAL exercises,
  signatures, or hashes as stronger evidence than their owning theorem says.
- Do not run massive proof builds on nextop while the remote builders are
  available.

## The decision rule

Prefer work that shortens the path from a real request to a reopenable receipt.
For every proposed lane ask, in order:

1. Does it make the statement smaller or more exact?
2. Does it instantiate a named trust/security boundary?
3. Does it connect a proved layer to a running consumer?
4. Does it add a refusal tooth or exact reproducible evidence?

If all four answers are no, it is probably not the next thing.
