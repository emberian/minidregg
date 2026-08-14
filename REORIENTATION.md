# Reorientation — 2026-08-14

This is a thin cross-repository orientation note, not another evidence ledger.
For research conclusions, `~/dev/zkml-research/docs/VERDICTS.md` is the single
current-truth file.  For exact proof/build evidence, use each repository's own
ledger at the commit being claimed.

Snapshot inspected while writing this note (and refreshed after the first
authorized audit-turn convergence):

- `minidregg` `907e880` on `main`, with an independently owned Uwueave
  Projection-V2/generated-Rust lane still active in the shared worktree;
- `zkml-research` `283692e` on `dev`, with active verdict/grinding notes and
  `vendor/` untracked; and
- `leanuweave` `a80a29b` on `dev`, with active durable-artifact,
  runtime-auth-V4, debt-gate, and Rust persistence work.

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
- the retained raw equivocation exposes an exact level and two distinct flat
  hash preimages with the same root.  This is a real witness-level reduction,
  but not yet the deployed Merkle/sponge/ROM reduction.

There is also now one deliberately tiny semantic floor in
`Assurance/ZkmlMatmulAuditTurn.lean`.  A fixed 2-by-2 F7 contraction has exact
output, three root-bound MLE claims, an accepted contraction sumcheck, and its
explicitly useless toy BaseFold budget carried as evidence on the same exact
authorized `CommittedTurn`.  Its four canonical result bytes and versioned
audit identity install atomically through `DurableDataIntent`; retry reopens
the identical envelope and altered audit bytes conflict.  The adjacent forged
output is refused.  Exact committed-source persvati run
`E-20260814T062149-52844-persvati-907e880f43e1-lake` built the target in 3,006
jobs with runner, command, and source-integrity exits zero.

That floor is exact recomputation, not the final succinct/deployment slice.
The remaining boundary is therefore narrower and more concrete:

1. **`[COMMIT-CR]`:** instantiate the actual Merkle/sponge opening scheme and
   reduce every retained position equivocation to a collision, while pinning
   the root/path codec and its byte/work cost;
2. **BCS/Fiat--Shamir:** encode the exact BaseFold oracle-message alphabet
   (level roots, sumcheck polynomials, openings, query seeds, and domain
   separators), then transport the interactive event through the ROM game with
   its hash/grinding terms still visible;
3. **succinct matmul composition:** replace the exact-recompute evidence with
   one serialized statement and executable checker that binds the C/A/B
   openings, contraction transcript, suite/registry identity, and complete
   named failure budget; and
4. **real crossings:** bind the selected Preoscript plan artifact and native
   candidate/proof bytes to that exact request without granting either
   authority, then replace the four-byte fixture codec/list registry with
   versioned deployed codecs, authenticated policy, and a physical persistence
   refinement whose claim ceiling stays explicit.

`HalfThresholdFriTranscript` owns the raw opened-fibre/equivocation split;
`HalfThresholdFriQuery` and `HalfThresholdFriCoherent` own the adaptive and
coherent sampled bounds.  Reuse them.  `Assurance/TwoRegimeQueryBudget.lean` is
now landed: for the current IRv2 regime it reports 34/73/130 bits under the
UDR/JBR/withdrawn-CBR models respectively, so only the withdrawn model reaches
128 bits.  This is configuration evidence and a refusal tooth, not permission
to promote the withdrawn assumption into a cryptographic claim.

## One system, four responsibilities

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
Selvage proof or commit-and-audit evidence
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
  priced `(2,57,16)` as prover-cheaper but verifier/wire-heavier; it is not
  landed, and the recursion verifier must first pin `num_queries` instead of
  reading the security parameter from the child proof.
- **Selvage's multilinear candidate** is BaseFold over Reed--Solomon in the
  unconditional `(1−ρ)/3` band.  Its deployment target must use the selected
  zkML field/extension and Poseidon2 commitment encoding (or explicitly choose
  and register another suite).  The existing Tower256/cSHAKE additive-FRI raw
  controller is a valuable implementation and reduction pattern, not a
  drop-in zkML PCS instance.

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
3. Continue from the now-landed raw `OpeningScheme` theorem and flat-hash
   collision witness: instantiate the intended BabyBear-extension/Poseidon2
   Merkle suite and discharge its retained equivocation branch there. Reuse
   the existing commitment, BCS, RBR-to-Fiat--Shamir, and ROM abstractions and
   the Tower256 raw controller's reduction pattern; do not relabel that
   cSHAKE/Tower256 suite as the zkML deployment or invent a KZG-shaped PCS
   abstraction merely to look multilinear.
4. Serialize the exact verifier alphabet and replace the exact-audit evidence
   with a runnable checker binding the three matmul openings,
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
