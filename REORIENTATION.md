# Reorientation — 2026-08-14

This is a thin cross-repository orientation note, not another evidence ledger.
For research conclusions, `~/dev/zkml-research/docs/VERDICTS.md` is the single
current-truth file.  For exact proof/build evidence, use each repository's own
ledger at the commit being claimed.

Snapshot inspected while writing this note (and refreshed after the BaseFold
commitment/query convergence):

- `minidregg` `1610755` on `main`, with an independently owned Uwueave
  Projection-V2/generated-Rust lane still active in the shared worktree;
- `zkml-research` `9be47ff` on `dev`, with `vendor/` and research notes
  untracked; and
- `lean-uwueave` `f9396b1` on `dev`, with active finite-history,
  finite-product, audit, and benchmark work.

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
  algebraic term and must not be counted as an opening.

The committed result is still an interactive, perfectly position-binding IOR
statement, not a deployment claim.  The raw opening layer now retains a
concrete `PositionEquivocation` witness instead of assuming it away, and the
equivocation branch is inhabited by an explicit bad scheme.  What remains is
therefore narrower and more cryptographic/semantic:

1. **`[COMMIT-CR]`:** instantiate the actual Merkle/sponge opening scheme and
   reduce every retained position equivocation to a collision, while pinning
   the root/path codec and its byte/work cost;
2. **BCS/Fiat--Shamir:** encode the exact BaseFold oracle-message alphabet
   (level roots, sumcheck polynomials, openings, query seeds, and domain
   separators), then transport the interactive event through the ROM game with
   its hash/grinding terms still visible;
3. **matmul composition:** bind the C/A/B claims and contraction sumcheck into
   one statement/checker/registry receipt rather than merely adding their
   theorem bounds in prose; and
4. **semantic durability:** authorize that exact checked statement, emit one
   canonical receipt, append it, and reopen the same receipt through the real
   durable-history path.

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

## Immediate convergence order

1. Preserve the now-landed contraction statement/native conformance seam and
   its explicit padding, PCS, Fiat--Shamir, and registry residuals.
2. Replace the accidental Projection-V2 bridge decision with an explicit
   interface choice. Use V3 for rich checked plan/result/certificate data;
   use the V4 sidecar only where context-bound runtime-auth facts are actually
   required. In both cases the imported value remains neutral data.
3. Put the now-landed committed/coherent BaseFold event behind the raw
   `OpeningScheme` boundary, and discharge its retained equivocation branch for
   one concrete Merkle/sponge suite. Reuse the existing commitment, BCS,
   RBR-to-Fiat--Shamir, and ROM cone; do not invent a second PCS abstraction
   merely to look multilinear.
4. Serialize the exact verifier alphabet and bind the three matmul openings,
   contraction claim, registry entry, checker version, and complete named
   failure budget into one statement. Then instantiate the audit checker's
   transport obligations and real beacon term.
5. Join that checked evidence to one canonical computation receipt and the
   existing durable history path. Only after this is green should the slice widen to
   nonlinearities, multiple layers, low-rank training deltas, or encrypted
   computation.

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
